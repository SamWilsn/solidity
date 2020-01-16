/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
/**
 * Analyzer part of inline assembly.
 */

#include <libyul/AsmAnalysis.h>

#include <libyul/AsmData.h>
#include <libyul/AsmScopeFiller.h>
#include <libyul/AsmScope.h>
#include <libyul/AsmAnalysisInfo.h>
#include <libyul/Utilities.h>
#include <libyul/Exceptions.h>
#include <libyul/Object.h>

#include <liblangutil/ErrorReporter.h>

#include <boost/range/adaptor/reversed.hpp>
#include <boost/algorithm/string.hpp>

#include <memory>
#include <functional>
#include <utility>

using namespace std;
using namespace solidity;
using namespace solidity::yul;
using namespace solidity::util;
using namespace solidity::langutil;

bool AsmAnalyzer::analyze(Block const& _block)
{
	bool success = false;
	try
	{
		if (!(ScopeFiller(m_info, m_errorReporter))(_block))
			return false;

		success = (*this)(_block);
		if (!success)
			yulAssert(m_errorReporter.hasErrors(), "No success but no error.");
	}
	catch (FatalError const&)
	{
		// This FatalError con occur if the errorReporter has too many errors.
		yulAssert(!m_errorReporter.errors().empty(), "Fatal error detected, but no error is reported.");
	}
	return success && !m_errorReporter.hasErrors();
}

AsmAnalysisInfo AsmAnalyzer::analyzeStrictAssertCorrect(Dialect const& _dialect, Object const& _object)
{
	ErrorList errorList;
	langutil::ErrorReporter errors(errorList);
	AsmAnalysisInfo analysisInfo;
	bool success = yul::AsmAnalyzer(
		analysisInfo,
		errors,
		_dialect,
		{},
		_object.dataNames()
	).analyze(*_object.code);
	yulAssert(success && errorList.empty(), "Invalid assembly/yul code.");
	return analysisInfo;
}

bool AsmAnalyzer::operator()(Literal const& _literal)
{
	expectValidType(_literal.type, _literal.location);
	++m_stackHeight;
	if (_literal.kind == LiteralKind::String && _literal.value.str().size() > 32)
	{
		m_errorReporter.typeError(
			_literal.location,
			"String literal too long (" + to_string(_literal.value.str().size()) + " > 32)"
		);
		return false;
	}
	else if (_literal.kind == LiteralKind::Number && bigint(_literal.value.str()) > u256(-1))
	{
		m_errorReporter.typeError(
			_literal.location,
			"Number literal too large (> 256 bits)"
		);
		return false;
	}
	else if (_literal.kind == LiteralKind::Boolean)
		yulAssert(_literal.value == "true"_yulstring || _literal.value == "false"_yulstring, "");

	if (!m_dialect.validTypeForLiteral(_literal.kind, _literal.value, _literal.type))
		m_errorReporter.typeError(
			_literal.location,
			"Invalid type \"" + _literal.type.str() + "\" for literal \"" + _literal.value.str() + "\"."
		);
	m_info.stackHeightInfo[&_literal] = m_stackHeight;
	m_typeOfCurrentExpression = {_literal.type};
	return true;
}

bool AsmAnalyzer::operator()(Identifier const& _identifier)
{
	yulAssert(!_identifier.name.empty(), "");
	size_t numErrorsBefore = m_errorReporter.errors().size();
	bool success = true;

	m_typeOfCurrentExpression = {m_dialect.defaultType};
	if (m_currentScope->lookup(_identifier.name, GenericVisitor{
		[&](Scope::Variable const& _var)
		{
			if (!m_activeVariables.count(&_var))
			{
				m_errorReporter.declarationError(
					_identifier.location,
					"Variable " + _identifier.name.str() + " used before it was declared."
				);
				success = false;
			}
			m_typeOfCurrentExpression = {_var.type};
			++m_stackHeight;
		},
		[&](Scope::Function const&)
		{
			m_errorReporter.typeError(
				_identifier.location,
				"Function " + _identifier.name.str() + " used without being called."
			);
			success = false;
		}
	}))
	{
	}
	else
	{
		size_t stackSize(-1);
		if (m_resolver)
		{
			bool insideFunction = m_currentScope->insideFunction();
			stackSize = m_resolver(_identifier, yul::IdentifierContext::RValue, insideFunction);
		}
		if (stackSize == size_t(-1))
		{
			// Only add an error message if the callback did not do it.
			if (numErrorsBefore == m_errorReporter.errors().size())
				m_errorReporter.declarationError(_identifier.location, "Identifier not found.");
			success = false;
		}
		m_stackHeight += stackSize == size_t(-1) ? 1 : stackSize;
	}
	m_info.stackHeightInfo[&_identifier] = m_stackHeight;

	return success;
}

bool AsmAnalyzer::operator()(ExpressionStatement const& _statement)
{
	int initialStackHeight = m_stackHeight;
	bool success = std::visit(*this, _statement.expression);
	if (success && m_stackHeight != initialStackHeight)
	{
		string msg =
			"Top-level expressions are not supposed to return values (this expression returns " +
			to_string(m_stackHeight - initialStackHeight) +
			" value" +
			(m_stackHeight - initialStackHeight == 1 ? "" : "s") +
			"). Use ``pop()`` or assign them.";
		m_errorReporter.error(Error::Type::TypeError, _statement.location, msg);
		success = false;
	}
	m_info.stackHeightInfo[&_statement] = m_stackHeight;
	return success;
}

bool AsmAnalyzer::operator()(Assignment const& _assignment)
{
	yulAssert(_assignment.value, "");
	int const expectedItems = _assignment.variableNames.size();
	yulAssert(expectedItems >= 1, "");
	int const stackHeight = m_stackHeight;
	bool success = std::visit(*this, *_assignment.value);

	// TODO this might be fully replaced by m_typeOfCurrentExpression
	if ((m_stackHeight - stackHeight) != expectedItems)
	{
		m_errorReporter.declarationError(
			_assignment.location,
			"Variable count does not match number of values (" +
			to_string(expectedItems) +
			" vs. " +
			to_string(m_stackHeight - stackHeight) +
			")"
		);
		return false;
	}

	for (size_t i = 0; i < _assignment.variableNames.size(); ++i)
	{
		YulString givenType = m_dialect.defaultType;
		if (i < m_typeOfCurrentExpression.size())
			givenType = m_typeOfCurrentExpression[i];
		if (!checkAssignment(_assignment.variableNames[i], givenType))
			success = false;
	}
	m_info.stackHeightInfo[&_assignment] = m_stackHeight;
	return success;
}

bool AsmAnalyzer::operator()(VariableDeclaration const& _varDecl)
{
	bool success = true;
	int const numVariables = _varDecl.variables.size();
	if (m_resolver)
		for (auto const& variable: _varDecl.variables)
			// Call the resolver for variable declarations to allow it to raise errors on shadowing.
			m_resolver(
				yul::Identifier{variable.location, variable.name},
				yul::IdentifierContext::VariableDeclaration,
				m_currentScope->insideFunction()
			);
	if (_varDecl.value)
	{
		int const stackHeight = m_stackHeight;
		success = std::visit(*this, *_varDecl.value);
		int numValues = m_stackHeight - stackHeight;
		if (numValues != numVariables)
		{
			m_errorReporter.declarationError(_varDecl.location,
				"Variable count mismatch: " +
				to_string(numVariables) +
				" variables and " +
				to_string(numValues) +
				" values."
			);
			// Adjust stack height to avoid misleading additional errors.
			m_stackHeight += numVariables - numValues;
			return false;
		}

		for (size_t i = 0; i < _varDecl.variables.size(); ++i)
		{
			YulString givenType = m_dialect.defaultType;
			if (i < m_typeOfCurrentExpression.size())
				givenType = m_typeOfCurrentExpression[i];
			TypedName const& variable = _varDecl.variables[i];
			expectValidType(variable.type, variable.location);
			if (variable.type != givenType)
			{
				m_errorReporter.typeError(
					variable.location,
					"Assigning value of type \"" + givenType.str() + "\" to variable of type \"" + variable.type.str() + "."
				);
				success = false;
			}
		}
	}
	else
		m_stackHeight += numVariables;

	for (TypedName const& variable: _varDecl.variables)
		m_activeVariables.insert(&std::get<Scope::Variable>(
			m_currentScope->identifiers.at(variable.name))
		);

	m_info.stackHeightInfo[&_varDecl] = m_stackHeight;
	return success;
}

bool AsmAnalyzer::operator()(FunctionDefinition const& _funDef)
{
	yulAssert(!_funDef.name.empty(), "");
	Block const* virtualBlock = m_info.virtualBlocks.at(&_funDef).get();
	yulAssert(virtualBlock, "");
	Scope& varScope = scope(virtualBlock);
	for (auto const& var: _funDef.parameters + _funDef.returnVariables)
	{
		expectValidType(var.type, var.location);
		m_activeVariables.insert(&std::get<Scope::Variable>(varScope.identifiers.at(var.name)));
	}

	int const stackHeight = m_stackHeight;
	m_stackHeight = _funDef.parameters.size() + _funDef.returnVariables.size();

	bool success = (*this)(_funDef.body);

	m_stackHeight = stackHeight;
	m_info.stackHeightInfo[&_funDef] = m_stackHeight;
	return success;
}

bool AsmAnalyzer::operator()(FunctionCall const& _funCall)
{
	yulAssert(!_funCall.functionName.name.empty(), "");
	bool success = true;
	vector<YulString> const* parameterTypes = nullptr;
	vector<YulString> const* returnTypes = nullptr;
	bool needsLiteralArguments = false;

	if (BuiltinFunction const* f = m_dialect.builtin(_funCall.functionName.name))
	{
		parameterTypes = &f->parameters;
		returnTypes = &f->returns;
		if (f->literalArguments)
			needsLiteralArguments = true;
	}
	else if (!m_currentScope->lookup(_funCall.functionName.name, GenericVisitor{
		[&](Scope::Variable const&)
		{
			m_errorReporter.typeError(
				_funCall.functionName.location,
				"Attempt to call variable instead of function."
			);
			success = false;
		},
		[&](Scope::Function const& _fun)
		{
			parameterTypes = &_fun.arguments;
			returnTypes = &_fun.returns;
		}
	}))
	{
		if (!warnOnInstructions(_funCall.functionName.name.str(), _funCall.functionName.location))
			m_errorReporter.declarationError(_funCall.functionName.location, "Function not found.");
		success = false;
	}
	if (success)
		if (_funCall.arguments.size() != parameterTypes->size())
		{
			m_errorReporter.typeError(
				_funCall.functionName.location,
				"Function expects " +
				to_string(parameterTypes->size()) +
				" arguments but got " +
				to_string(_funCall.arguments.size()) + "."
			);
			success = false;
		}

	vector<YulString> argTypes;
	for (auto const& arg: _funCall.arguments | boost::adaptors::reversed)
	{
		if (!expectExpression(arg))
		{
			success = false;
			continue;
		}
		argTypes.emplace_back(m_typeOfCurrentExpression.at(0));

		if (needsLiteralArguments)
		{
			if (!holds_alternative<Literal>(arg))
				m_errorReporter.typeError(
					_funCall.functionName.location,
					"Function expects direct literals as arguments."
				);
			else if (!m_dataNames.count(std::get<Literal>(arg).value))
				m_errorReporter.typeError(
					_funCall.functionName.location,
					"Unknown data object \"" + std::get<Literal>(arg).value.str() + "\"."
				);
		}
	}

	if (success)
	{
		yulAssert(parameterTypes && parameterTypes->size() == argTypes.size(), "");
		for (size_t i = 0; i < parameterTypes->size(); ++i)
			if (!expectType((*parameterTypes)[i], argTypes[i], locationOf(_funCall.arguments[i])))
				success = false;
	}
	// Use argument size instead of parameter count to avoid misleading errors.
	m_stackHeight += int(returnTypes ? returnTypes->size() : 0) - int(_funCall.arguments.size());
	m_info.stackHeightInfo[&_funCall] = m_stackHeight;
	if (success)
	{
		yulAssert(returnTypes, "");
		m_typeOfCurrentExpression = *returnTypes;
	}
	else if (returnTypes)
		m_typeOfCurrentExpression = vector<YulString>(returnTypes->size(), m_dialect.defaultType);
	else
		m_typeOfCurrentExpression = {};
	return success;
}

bool AsmAnalyzer::operator()(If const& _if)
{
	bool success = true;

	int const initialHeight = m_stackHeight;
	// TODO might expect type directly
	if (!expectExpression(*_if.condition))
		success = false;
	else if (!expectType(m_dialect.boolType, m_typeOfCurrentExpression.at(0), locationOf(*_if.condition)))
		success = false;

	m_stackHeight = initialHeight;

	if (!(*this)(_if.body))
		success = false;

	m_info.stackHeightInfo[&_if] = m_stackHeight;

	return success;
}

bool AsmAnalyzer::operator()(Switch const& _switch)
{
	yulAssert(_switch.expression, "");

	bool success = true;

	int const initialHeight = m_stackHeight;
	if (!expectExpression(*_switch.expression))
		success = false;

	YulString valueType = m_dialect.defaultType;
	if (success)
		valueType = m_typeOfCurrentExpression.at(0);

	for (auto const& _case: _switch.cases)
		if (_case.value)
			if (!expectType(valueType, _case.value->type, _case.value->location))
				success = false;

	set<u256> cases;
	for (auto const& _case: _switch.cases)
	{
		if (_case.value)
		{
			int const initialStackHeight = m_stackHeight;
			bool isCaseValueValid = true;
			// We cannot use "expectExpression" here because *_case.value is not a
			// Statement and would be converted to a Statement otherwise.
			if (!(*this)(*_case.value))
			{
				isCaseValueValid = false;
				success = false;
			}
			expectDeposit(1, initialStackHeight, _case.value->location);
			m_stackHeight--;

			// If the case value is not valid, we should not insert it into cases.
			yulAssert(isCaseValueValid || m_errorReporter.hasErrors(), "Invalid case value.");
			/// Note: the parser ensures there is only one default case
			if (isCaseValueValid && !cases.insert(valueOfLiteral(*_case.value)).second)
			{
				m_errorReporter.declarationError(
					_case.location,
					"Duplicate case defined."
				);
				success = false;
			}
		}

		if (!(*this)(_case.body))
			success = false;
	}

	m_stackHeight = initialHeight;
	m_info.stackHeightInfo[&_switch] = m_stackHeight;

	return success;
}

bool AsmAnalyzer::operator()(ForLoop const& _for)
{
	yulAssert(_for.condition, "");

	Scope* outerScope = m_currentScope;

	int const initialHeight = m_stackHeight;

	bool success = true;
	if (!(*this)(_for.pre))
		success = false;
	// The block was closed already, but we re-open it again and stuff the
	// condition, the body and the post part inside.
	m_stackHeight += scope(&_for.pre).numberOfVariables();
	m_currentScope = &scope(&_for.pre);

	if (!expectExpression(*_for.condition))
		success = false;
	else if (!expectType(m_dialect.boolType, m_typeOfCurrentExpression.at(0), locationOf(*_for.condition)))
		success = false;

	m_stackHeight--;

	// backup outer for-loop & create new state
	auto outerForLoop = m_currentForLoop;
	m_currentForLoop = &_for;

	if (!(*this)(_for.body))
		success = false;

	if (!(*this)(_for.post))
		success = false;

	m_stackHeight = initialHeight;
	m_info.stackHeightInfo[&_for] = m_stackHeight;
	m_currentScope = outerScope;
	m_currentForLoop = outerForLoop;

	return success;
}

bool AsmAnalyzer::operator()(Break const& _break)
{
	m_info.stackHeightInfo[&_break] = m_stackHeight;
	return true;
}

bool AsmAnalyzer::operator()(Continue const& _continue)
{
	m_info.stackHeightInfo[&_continue] = m_stackHeight;
	return true;
}

bool AsmAnalyzer::operator()(Leave const& _leaveStatement)
{
	m_info.stackHeightInfo[&_leaveStatement] = m_stackHeight;
	return true;
}

bool AsmAnalyzer::operator()(Block const& _block)
{
	bool success = true;
	auto previousScope = m_currentScope;
	m_currentScope = &scope(&_block);

	int const initialStackHeight = m_stackHeight;

	for (auto const& s: _block.statements)
		if (!std::visit(*this, s))
			success = false;

	m_stackHeight -= scope(&_block).numberOfVariables();

	int const stackDiff = m_stackHeight - initialStackHeight;
	if (success && stackDiff != 0)
	{
		m_errorReporter.declarationError(
			_block.location,
			"Unbalanced stack at the end of a block: " +
			(
				stackDiff > 0 ?
				to_string(stackDiff) + string(" surplus item(s).") :
				to_string(-stackDiff) + string(" missing item(s).")
			)
		);
		success = false;
	}

	m_info.stackHeightInfo[&_block] = m_stackHeight;
	m_currentScope = previousScope;
	return success;
}

bool AsmAnalyzer::expectExpression(Expression const& _expr)
{
	bool success = true;
	int const initialHeight = m_stackHeight;
	if (!std::visit(*this, _expr))
		success = false;
	if (success && !expectDeposit(1, initialHeight, locationOf(_expr)))
		success = false;
	return success;
}

bool AsmAnalyzer::expectDeposit(int _deposit, int _oldHeight, SourceLocation const& _location)
{
	if (m_stackHeight - _oldHeight != _deposit)
	{
		m_errorReporter.typeError(
			_location,
			"Expected expression to return one item to the stack, but did return " +
			to_string(m_stackHeight - _oldHeight) +
			" items."
		);
		return false;
	}
	return true;
}

bool AsmAnalyzer::checkAssignment(Identifier const& _variable, YulString _valueType)
{
	yulAssert(!_variable.name.empty(), "");
	bool success = true;
	size_t numErrorsBefore = m_errorReporter.errors().size();
	size_t variableSize(-1);
	YulString variableType = m_dialect.defaultType;
	if (Scope::Identifier const* var = m_currentScope->lookup(_variable.name))
	{
		// Check that it is a variable
		if (!holds_alternative<Scope::Variable>(*var))
		{
			m_errorReporter.typeError(_variable.location, "Assignment requires variable.");
			success = false;
		}
		else if (!m_activeVariables.count(&std::get<Scope::Variable>(*var)))
		{
			m_errorReporter.declarationError(
				_variable.location,
				"Variable " + _variable.name.str() + " used before it was declared."
			);
			success = false;
		}
		else
			variableType = std::get<Scope::Variable>(*var).type;

		variableSize = 1;
	}
	else if (m_resolver)
	{
		bool insideFunction = m_currentScope->insideFunction();
		variableSize = m_resolver(_variable, yul::IdentifierContext::LValue, insideFunction);
	}
	if (variableSize == size_t(-1))
	{
		// Only add message if the callback did not.
		if (numErrorsBefore == m_errorReporter.errors().size())
			m_errorReporter.declarationError(_variable.location, "Variable not found or variable not lvalue.");
		success = false;
	}

	m_stackHeight --;

	if (variableSize != 1 && variableSize != size_t(-1))
	{
		m_errorReporter.typeError(
			_variable.location,
			"Variable size (" +
			to_string(variableSize) +
			") and value size (1) do not match."
		);
		success = false;
	}

	if (success && variableType != _valueType)
	{
		m_errorReporter.typeError(_variable.location,
			"Assigning a value of type \"" +
			_valueType.str() +
			"\" to a variable of type \"" +
			variableType.str() +
			"\"."
		);
		success = false;
	}

	return success;
}

Scope& AsmAnalyzer::scope(Block const* _block)
{
	yulAssert(m_info.scopes.count(_block) == 1, "Scope requested but not present.");
	auto scopePtr = m_info.scopes.at(_block);
	yulAssert(scopePtr, "Scope requested but not present.");
	return *scopePtr;
}
void AsmAnalyzer::expectValidType(YulString _type, SourceLocation const& _location)
{
	if (!m_dialect.types.count(_type))
		m_errorReporter.typeError(
			_location,
			"\"" + _type.str() + "\" is not a valid type (user defined types are not yet supported)."
		);
}

// TODO might be better to use Expression instead of location so that location extraction is only needed in error case.
bool AsmAnalyzer::expectType(YulString _expectedType, YulString _givenType, SourceLocation const& _location)
{
	if (_expectedType != _givenType)
	{
		m_errorReporter.typeError(_location,
			"Expected a value of type \"" +
			_expectedType.str() +
			"\" but got \"" +
			_givenType.str()
		);
		return false;
	}
	return true;
}

bool AsmAnalyzer::warnOnInstructions(std::string const& _instructionIdentifier, langutil::SourceLocation const& _location)
{
	auto const builtin = EVMDialect::strictAssemblyForEVM(EVMVersion{}).builtin(YulString(_instructionIdentifier));
	if (builtin)
		return warnOnInstructions(builtin->instruction.value(), _location);
	else
		return false;
}

bool AsmAnalyzer::warnOnInstructions(evmasm::Instruction _instr, SourceLocation const& _location)
{
	// We assume that returndatacopy, returndatasize and staticcall are either all available
	// or all not available.
	yulAssert(m_evmVersion.supportsReturndata() == m_evmVersion.hasStaticCall(), "");
	// Similarly we assume bitwise shifting and create2 go together.
	yulAssert(m_evmVersion.hasBitwiseShifting() == m_evmVersion.hasCreate2(), "");

	auto errorForVM = [=](string const& vmKindMessage) {
		m_errorReporter.typeError(
			_location,
			"The \"" +
			boost::to_lower_copy(instructionInfo(_instr).name)
			+ "\" instruction is " +
			vmKindMessage +
			" VMs " +
			" (you are currently compiling for \"" +
			m_evmVersion.name() +
			"\")."
		);
	};

	if ((
		_instr == evmasm::Instruction::RETURNDATACOPY ||
		_instr == evmasm::Instruction::RETURNDATASIZE
	) && !m_evmVersion.supportsReturndata())
	{
		errorForVM("only available for Byzantium-compatible");
	}
	else if (_instr == evmasm::Instruction::STATICCALL && !m_evmVersion.hasStaticCall())
	{
		errorForVM("only available for Byzantium-compatible");
	}
	else if ((
		_instr == evmasm::Instruction::SHL ||
		_instr == evmasm::Instruction::SHR ||
		_instr == evmasm::Instruction::SAR
	) && !m_evmVersion.hasBitwiseShifting())
	{
		errorForVM("only available for Constantinople-compatible");
	}
	else if (_instr == evmasm::Instruction::CREATE2 && !m_evmVersion.hasCreate2())
	{
		errorForVM("only available for Constantinople-compatible");
	}
	else if (_instr == evmasm::Instruction::EXTCODEHASH && !m_evmVersion.hasExtCodeHash())
	{
		errorForVM("only available for Constantinople-compatible");
	}
	else if (_instr == evmasm::Instruction::CHAINID && !m_evmVersion.hasChainID())
	{
		errorForVM("only available for Istanbul-compatible");
	}
	else if (_instr == evmasm::Instruction::SELFBALANCE && !m_evmVersion.hasSelfBalance())
	{
		errorForVM("only available for Istanbul-compatible");
	}
	else if (
		_instr == evmasm::Instruction::JUMP ||
		_instr == evmasm::Instruction::JUMPI ||
		_instr == evmasm::Instruction::JUMPDEST
	)
	{
		m_errorReporter.error(
			Error::Type::SyntaxError,
			_location,
			"Jump instructions and labels are low-level EVM features that can lead to "
			"incorrect stack access. Because of that they are disallowed in strict assembly. "
			"Use functions, \"switch\", \"if\" or \"for\" statements instead."
		);
	}
	else
		return false;

	return true;
}
