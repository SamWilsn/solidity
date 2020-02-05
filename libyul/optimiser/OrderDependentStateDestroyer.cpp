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
 * Optimiser component that destroys order-dependent state accesses.
 */

#include <libyul/AsmPrinter.h>
#include "libyul/Dialect.h"
#include "libyul/YulString.h"
#include "libyul/backends/evm/EVMDialect.h"
#include "libyul/optimiser/ASTWalker.h"
#include <algorithm>
#include <boost/range/adaptor/reversed.hpp>

#include <cstddef>
#include <deque>
#include <iostream>
#include <iterator>
#include <libevmasm/Instruction.h>
#include <libyul/Exceptions.h>
#include <libsolutil/Assertions.h>
#include <libyul/AsmDataForward.h>
#include <libyul/optimiser/OrderDependentStateDestroyer.h>
#include <libyul/optimiser/Semantics.h>
#include <libyul/AsmData.h>

#include <libsolutil/CommonData.h>

#include <boost/range/algorithm_ext/erase.hpp>
#include <map>
#include <memory>
#include <optional>
#include <ostream>
#include <set>
#include <stack>
#include <stdexcept>
#include <unordered_map>
#include <utility>
#include <variant>
#include <vector>

using namespace std;
using namespace solidity;
using namespace solidity::yul;

static const YulString MAIN("!!main");

struct CallSite
{
    YulString callee;
    std::vector<std::optional<YulString>> arguments;
    std::vector<YulString> returns;
};

enum class Virtue { Clean = 0, Undecided, Tainted };

class Variable
{
public:
    Variable(YulString _name, Virtue _virtue = Virtue::Undecided):
        m_name(_name), m_virtue(_virtue), m_protected(false) {}

    Virtue virtue() const { return m_virtue; }
    const char* virtue_str() const
    {
        switch (m_virtue)
        {
            case Virtue::Undecided:
                return "Undecided";
            case Virtue::Clean:
                return "Clean";
            case Virtue::Tainted:
                return "Tainted";
            default:
                return "";
        }
    }

    bool isProtected() const { return m_protected; }

    void setProtected()
    {
        m_protected = true;
    }

    void setTainted()
    {
        m_virtue = Virtue::Tainted;
    }

    void setClean()
    {
        switch (m_virtue)
        {
            case Virtue::Clean:
            case Virtue::Undecided:
                m_virtue = Virtue::Clean;
                break;

            default:
                assertThrow(false, OptimizerException, "conflict: already tainted");
                break;
        }
    }

private:
    Variable() = delete;

    YulString m_name;
    Virtue m_virtue;
    bool m_protected;
};

class FunctionScope;

class State
{
public:
    static std::shared_ptr<State> make_shared(Dialect const& _dialect);

    State() = delete;

    Dialect const& dialect() { return m_dialect; }

    FunctionScope const& function(YulString const& _name) const { return m_functions.at(_name); }
    FunctionScope& function(YulString const& _name) { return m_functions.at(_name); }
    FunctionScope& addFunction(FunctionScope scope);

    Variable& addVariable(YulString _name);
    void taintVariable(YulString const& _name);
    void protectVariable(YulString const& _name);
    void protectVariable(Expression const& _expr);
    YulString duplicateVariable(YulString const& _name);
    std::set<YulString> taintedVariables() const;

	void enterAssignment(std::vector<YulString>);
	void leaveAssignment(std::vector<YulString> const&);
    std::vector<YulString> const& currentAssignment() const;

    void dump() const;

    void resolve();
    void verify() const;

private:
    unsigned int m_rename;

    Dialect const& m_dialect;
    std::map<YulString, Variable> m_variables;
    std::vector<YulString> m_current_assignment;
    std::map<YulString, FunctionScope> m_functions;

    explicit State(Dialect const&);
};

State::State(Dialect const& _dialect): m_rename(0), m_dialect(_dialect)
{
}

std::set<YulString> State::taintedVariables() const
{
    std::set<YulString> tainted;

    for (auto const& kv: m_variables)
    {
        if (kv.second.virtue() == Virtue::Tainted)
        {
            tainted.insert(kv.first);
        }
    }

    return tainted;
}

YulString State::duplicateVariable(YulString const& _name)
{
    std::stringstream ss;
    ss << _name.str() << "_" << m_rename;
    YulString new_name = YulString(ss.str());

    m_rename += 1;

    addVariable(new_name) = m_variables.at(_name);

    return new_name;
}

void State::taintVariable(YulString const& _name)
{
    m_variables.at(_name).setTainted();
}

void State::protectVariable(YulString const& _name)
{
    m_variables.at(_name).setProtected();
}

void State::protectVariable(Expression const& _expr)
{
    if (holds_alternative<Literal>(_expr)) return;
    assertThrow(holds_alternative<Identifier>(_expr), OptimizerException, "untaintable non-ident");

    Identifier const& ident = std::get<Identifier>(_expr);
    protectVariable(ident.name);
}

Variable& State::addVariable(YulString _name)
{
    Variable var(_name);

    auto result = m_variables.emplace(std::make_pair(_name, var));
    assertThrow(result.second, OptimizerException, "duplicate variable");

    return m_variables.at(_name);
}

void State::enterAssignment(std::vector<YulString> _vars)
{
    assertThrow(m_current_assignment.empty(), OptimizerException, "double assign");
    m_current_assignment = _vars;
}

void State::leaveAssignment(std::vector<YulString> const& _vars)
{
    assertThrow(!m_current_assignment.empty(), OptimizerException, "missing assign");
    assertThrow(_vars.size() == m_current_assignment.size(), OptimizerException, "mismatched assign");

    m_current_assignment.clear();
}

std::vector<YulString> const& State::currentAssignment() const
{
    return m_current_assignment;
}


class FunctionScope
{
public:
    explicit FunctionScope(std::weak_ptr<State> _state);
    FunctionScope(std::weak_ptr<State> _state, FunctionDefinition const& _funDef);

    YulString const& name() const { return m_name; }

    void operator()(Assignment const& _assignment);
    void operator()(VariableDeclaration const& _varDecl);
    void operator()(FunctionCall const& _funCall);

    void dump_state() const;

    bool isResolved() const { return m_unresolved_calls.empty(); }
    bool resolve();
    void propagateTaint();

private:
    std::weak_ptr<State> m_state;
    YulString m_name;

    std::map<YulString, std::set<YulString>> m_data_flow;
    std::vector<YulString> m_parameters;
    std::vector<YulString> m_returns;

    std::vector<CallSite> m_unresolved_calls;

    FunctionScope() = delete;

    void influences(YulString _upstream, YulString _downstream);
	void influences(Expression const& _upstream, YulString _downstream);

    void visitBuiltin(FunctionCall const& _funCall, BuiltinFunctionForEVM const* _builtin);
    void visitFunc(FunctionCall const&);

    void embed(FunctionScope const&, std::vector<std::optional<YulString>> const&, std::vector<YulString> const&);

    std::set<YulString> findDownstream(YulString const& _source) const;
};

FunctionScope::FunctionScope(std::weak_ptr<State> _state)
    : m_state(_state), m_name(MAIN)
{

}

FunctionScope::FunctionScope(std::weak_ptr<State> _state, FunctionDefinition const& _funDef)
    : m_state(_state), m_name(_funDef.name)
{
    std::shared_ptr<State> state(_state.lock());

    for (TypedName const& tn: _funDef.parameters)
    {
        state->addVariable(tn.name);
        m_parameters.emplace_back(tn.name);
    }

    for (TypedName const& tn: _funDef.returnVariables)
    {
        state->addVariable(tn.name);
        m_returns.emplace_back(tn.name);
    }
}

void FunctionScope::influences(YulString _upstream, YulString _downstream)
{
    m_data_flow[_upstream].emplace(_downstream);
}

void FunctionScope::influences(Expression const& _upstream, YulString _downstream)
{
    if (holds_alternative<Literal>(_upstream))
    {
        return;
    }

    assertThrow(holds_alternative<Identifier>(_upstream), OptimizerException, "upstream expr must be literal or identifier");
    Identifier const& upstream_ident = std::get<Identifier>(_upstream);

    influences(upstream_ident.name, _downstream);
}

void FunctionScope::operator()(Assignment const& _assignment)
{
    std::shared_ptr<State> state(m_state.lock());

    if (holds_alternative<Identifier>(*_assignment.value))
    {
        assertThrow(
            1 == _assignment.variableNames.size(),
            OptimizerException,
            "not enough variables to unpack (expected 1)"
        );

        Identifier const& ident = std::get<Identifier>(*_assignment.value);

		influences(ident.name, _assignment.variableNames[0].name);
	}
	else if (holds_alternative<Literal>(*_assignment.value))
    {
        assertThrow(
            1 == _assignment.variableNames.size(),
            OptimizerException,
            "not enough variables to unpack (expected 1)"
        );

        // TODO: Maybe setClean the variable
    }
    else if (holds_alternative<FunctionCall>(*_assignment.value))
    {
        FunctionCall const& call = std::get<FunctionCall>(*_assignment.value);

        std::vector<YulString> vars;
        for (Identifier const& ident: _assignment.variableNames)
        {
            vars.push_back(ident.name);
        }

        state->enterAssignment(vars);
        (*this)(call);
        state->leaveAssignment(vars);
    }
    else
    {
        assertThrow(false, OptimizerException, "unexpected assignment value");
    }

}

void FunctionScope::operator()(VariableDeclaration const& _varDecl)
{
    std::shared_ptr<State> state(m_state.lock());

    for (TypedName const& tn: _varDecl.variables)
    {
        state->addVariable(tn.name);
    }

    if (holds_alternative<Identifier>(*_varDecl.value))
    {
        assertThrow(
            1 == _varDecl.variables.size(),
            OptimizerException,
            "not enough variables to unpack (expected 1)"
        );

        Identifier const& ident = std::get<Identifier>(*_varDecl.value);
		influences(ident.name, _varDecl.variables[0].name);
	}
	else if (holds_alternative<Literal>(*_varDecl.value))
    {
        assertThrow(
            1 == _varDecl.variables.size(),
            OptimizerException,
            "not enough variables to unpack (expected 1)"
        );

        // TODO: Possibly setClean on the variable.
    }
    else if (holds_alternative<FunctionCall>(*_varDecl.value))
    {
        FunctionCall const& call = std::get<FunctionCall>(*_varDecl.value);

        std::vector<YulString> vars;
        for (TypedName const& tn: _varDecl.variables)
        {
            vars.push_back(tn.name);
        }

        state->enterAssignment(vars);
        (*this)(call);
        state->leaveAssignment(vars);
    }
    else
    {
        assertThrow(false, OptimizerException, "unexpected declaration value");
    }
}

void FunctionScope::operator()(FunctionCall const& _funCall)
{
    std::shared_ptr<State> state(m_state.lock());

    if (EVMDialect const* dialect = dynamic_cast<EVMDialect const*>(&state->dialect()))
    {
        if (auto const* builtin = dialect->builtin(_funCall.functionName.name))
        {
            visitBuiltin(_funCall, builtin);
        }
        else
        {
            visitFunc(_funCall);
        }
    }
    else
    {
        assertThrow(false, OptimizerException, "only EVM dialect is supported");
    }
}

void FunctionScope::visitFunc(FunctionCall const& _funCall)
{
    std::shared_ptr<State> state(m_state.lock());
    std::vector<std::optional<YulString>> args;

    for (Expression const& expr: _funCall.arguments)
    {
        if (holds_alternative<Literal>(expr))
        {
            std::optional<YulString> empty;
            args.push_back(empty);
        }
        else if (holds_alternative<Identifier>(expr))
        {
            Identifier const& ident = std::get<Identifier>(expr);
            args.push_back(ident.name);
        }
        else
        {
            assertThrow(false, OptimizerException, "unexpected function argument");
        }
    }

    CallSite cs;
    cs.callee = _funCall.functionName.name;
    cs.arguments = args;
    cs.returns = state->currentAssignment();

    m_unresolved_calls.push_back(cs);
}

void FunctionScope::visitBuiltin(FunctionCall const& _funCall, BuiltinFunctionForEVM const* _builtin)
{
    if (!_builtin->instruction)
    {
        std::cout << "Builtin with no instruction: " << _funCall.functionName.name.str() << std::endl;
        return;
    }

    std::shared_ptr<State> state(m_state.lock());
    std::vector<YulString> const& returns = state->currentAssignment();

    switch (*_builtin->instruction)
    {
        case evmasm::Instruction::STOP:
            break;

        case evmasm::Instruction::ADD:
        case evmasm::Instruction::MUL:
        case evmasm::Instruction::SUB:
        case evmasm::Instruction::DIV:
        case evmasm::Instruction::SDIV:
        case evmasm::Instruction::MOD:
        case evmasm::Instruction::SMOD:
        case evmasm::Instruction::EXP:
        case evmasm::Instruction::SIGNEXTEND:
        case evmasm::Instruction::LT:
        case evmasm::Instruction::GT:
        case evmasm::Instruction::SLT:
        case evmasm::Instruction::SGT:
        case evmasm::Instruction::EQ:
        case evmasm::Instruction::AND:
        case evmasm::Instruction::OR:
        case evmasm::Instruction::XOR:
        case evmasm::Instruction::BYTE:
        case evmasm::Instruction::SHL:
        case evmasm::Instruction::SHR:
        case evmasm::Instruction::SAR:
            influences(_funCall.arguments.at(0), returns.at(0));
            influences(_funCall.arguments.at(1), returns.at(0));
            break;

        case evmasm::Instruction::ADDMOD:
        case evmasm::Instruction::MULMOD:
            influences(_funCall.arguments.at(0), returns.at(0));
            influences(_funCall.arguments.at(1), returns.at(0));
            influences(_funCall.arguments.at(2), returns.at(0));
            break;

        case evmasm::Instruction::ISZERO:
        case evmasm::Instruction::NOT:
        case evmasm::Instruction::CALLDATALOAD:
        case evmasm::Instruction::BLOCKHASH:
            influences(_funCall.arguments.at(0), returns.at(0));
            break;

        case evmasm::Instruction::RETURN:
        case evmasm::Instruction::CREATE:
        case evmasm::Instruction::CREATE2:
        case evmasm::Instruction::MLOAD:
        case evmasm::Instruction::MSTORE:
        case evmasm::Instruction::MSTORE8:
        case evmasm::Instruction::RETURNDATACOPY:
        case evmasm::Instruction::EXTCODECOPY:
        case evmasm::Instruction::CODECOPY:
        case evmasm::Instruction::CALLDATACOPY:
        case evmasm::Instruction::KECCAK256:
            std::cout
                << "memory not supported ("
                << _funCall.functionName.name.str()
                << ")"
                << std::endl;
            break;

        case evmasm::Instruction::ADDRESS:
        case evmasm::Instruction::ORIGIN:
        case evmasm::Instruction::CALLER:
        case evmasm::Instruction::CALLVALUE:
        case evmasm::Instruction::CODESIZE:
        case evmasm::Instruction::GASPRICE:
        case evmasm::Instruction::CHAINID:
        case evmasm::Instruction::MSIZE:
            // TODO: Possibly setClean on the return value
            break;

        case evmasm::Instruction::EXTCODEHASH:
        case evmasm::Instruction::EXTCODESIZE:
        case evmasm::Instruction::BALANCE:
            state->taintVariable(returns.at(0));
            state->protectVariable(_funCall.arguments.at(0));

            influences(_funCall.arguments.at(0), returns.at(0));
            break;

        case evmasm::Instruction::GAS:
        case evmasm::Instruction::RETURNDATASIZE:
        case evmasm::Instruction::CALLDATASIZE:
        case evmasm::Instruction::COINBASE:
        case evmasm::Instruction::TIMESTAMP:
        case evmasm::Instruction::NUMBER:
        case evmasm::Instruction::DIFFICULTY:
        case evmasm::Instruction::GASLIMIT:
        case evmasm::Instruction::SELFBALANCE:
            state->taintVariable(returns.at(0));
            break;

        case evmasm::Instruction::JUMPDEST:
            break;

        case evmasm::Instruction::SLOAD:
            std::cout << "SLOAD tainting " << returns.at(0).str() << std::endl;
            state->taintVariable(returns.at(0));
            state->protectVariable(_funCall.arguments.at(0));
            influences(_funCall.arguments.at(0), returns.at(0));
            break;

        case evmasm::Instruction::SSTORE:
            state->protectVariable(_funCall.arguments.at(0));
            break;

        case evmasm::Instruction::JUMP:
        case evmasm::Instruction::JUMPI:
        case evmasm::Instruction::PC:
            assertThrow(false, OptimizerException, "$pc access not supported");
            break;

        case evmasm::Instruction::POP:
            std::cout << "pop?" << std::endl;
            // TODO: Stack manipulation isn't supported.
            break;

        case evmasm::Instruction::PUSH1:
        case evmasm::Instruction::PUSH2:
        case evmasm::Instruction::PUSH3:
        case evmasm::Instruction::PUSH4:
        case evmasm::Instruction::PUSH5:
        case evmasm::Instruction::PUSH6:
        case evmasm::Instruction::PUSH7:
        case evmasm::Instruction::PUSH8:
        case evmasm::Instruction::PUSH9:
        case evmasm::Instruction::PUSH10:
        case evmasm::Instruction::PUSH11:
        case evmasm::Instruction::PUSH12:
        case evmasm::Instruction::PUSH13:
        case evmasm::Instruction::PUSH14:
        case evmasm::Instruction::PUSH15:
        case evmasm::Instruction::PUSH16:
        case evmasm::Instruction::PUSH17:
        case evmasm::Instruction::PUSH18:
        case evmasm::Instruction::PUSH19:
        case evmasm::Instruction::PUSH20:
        case evmasm::Instruction::PUSH21:
        case evmasm::Instruction::PUSH22:
        case evmasm::Instruction::PUSH23:
        case evmasm::Instruction::PUSH24:
        case evmasm::Instruction::PUSH25:
        case evmasm::Instruction::PUSH26:
        case evmasm::Instruction::PUSH27:
        case evmasm::Instruction::PUSH28:
        case evmasm::Instruction::PUSH29:
        case evmasm::Instruction::PUSH30:
        case evmasm::Instruction::PUSH31:
        case evmasm::Instruction::PUSH32:

        case evmasm::Instruction::DUP1:
        case evmasm::Instruction::DUP2:
        case evmasm::Instruction::DUP3:
        case evmasm::Instruction::DUP4:
        case evmasm::Instruction::DUP5:
        case evmasm::Instruction::DUP6:
        case evmasm::Instruction::DUP7:
        case evmasm::Instruction::DUP8:
        case evmasm::Instruction::DUP9:
        case evmasm::Instruction::DUP10:
        case evmasm::Instruction::DUP11:
        case evmasm::Instruction::DUP12:
        case evmasm::Instruction::DUP13:
        case evmasm::Instruction::DUP14:
        case evmasm::Instruction::DUP15:
        case evmasm::Instruction::DUP16:

        case evmasm::Instruction::SWAP1:
        case evmasm::Instruction::SWAP2:
        case evmasm::Instruction::SWAP3:
        case evmasm::Instruction::SWAP4:
        case evmasm::Instruction::SWAP5:
        case evmasm::Instruction::SWAP6:
        case evmasm::Instruction::SWAP7:
        case evmasm::Instruction::SWAP8:
        case evmasm::Instruction::SWAP9:
        case evmasm::Instruction::SWAP10:
        case evmasm::Instruction::SWAP11:
        case evmasm::Instruction::SWAP12:
        case evmasm::Instruction::SWAP13:
        case evmasm::Instruction::SWAP14:
        case evmasm::Instruction::SWAP15:
        case evmasm::Instruction::SWAP16:
            assertThrow(false, OptimizerException, "stack not implemented");
            break;

        case evmasm::Instruction::LOG0:
        case evmasm::Instruction::LOG1:
        case evmasm::Instruction::LOG2:
        case evmasm::Instruction::LOG3:
        case evmasm::Instruction::LOG4:
            break;

        case evmasm::Instruction::JUMPTO:
        case evmasm::Instruction::JUMPIF:
        case evmasm::Instruction::JUMPV:
        case evmasm::Instruction::JUMPSUB:
        case evmasm::Instruction::JUMPSUBV:
        case evmasm::Instruction::BEGINSUB:
        case evmasm::Instruction::BEGINDATA:
        case evmasm::Instruction::RETURNSUB:
        case evmasm::Instruction::PUTLOCAL:
        case evmasm::Instruction::GETLOCAL:
            assertThrow(false, OptimizerException, "unknown instruction");
            break;

        case evmasm::Instruction::CALL:
        case evmasm::Instruction::STATICCALL:
        case evmasm::Instruction::CALLCODE:
        case evmasm::Instruction::DELEGATECALL:
            state->taintVariable(returns.at(0));
            break;

        case evmasm::Instruction::REVERT:
        case evmasm::Instruction::INVALID:
        case evmasm::Instruction::SELFDESTRUCT:
            break;
    }
}

bool FunctionScope::resolve()
{
    std::shared_ptr<State> state(m_state.lock());

    std::cout << "Resolving: " << m_name.str() << std::endl;

    while (!m_unresolved_calls.empty())
    {
        CallSite const& cs = m_unresolved_calls.back();
        FunctionScope const& callee = state->function(cs.callee);

        if (!callee.isResolved())
        {
            std::cout << "\tFailed: " << cs.callee.str() << std::endl;

            // Check if the callee function is fully resolved. If not, defer
            // resolving this function.

            // TODO: handle cycles in the call graph.
            return false;
        }

        embed(callee, cs.arguments, cs.returns);

        m_unresolved_calls.pop_back();
    }

    return true;
}

void FunctionScope::embed(FunctionScope const& _callee, std::vector<std::optional<YulString>> const& _args, std::vector<YulString> const& _returns)
{
    std::shared_ptr<State> state(m_state.lock());

    std::map<YulString, YulString> renames;

    // Rename parameters and influence them from the arguments.
    for (size_t ii = 0; ii < _callee.m_parameters.size(); ii++)
    {
        YulString const& param = _callee.m_parameters[ii];

        YulString new_name = state->duplicateVariable(param);
        auto ins = renames.emplace(std::make_pair(param, new_name));
        assertThrow(ins.second, OptimizerException, "duplicate rename");

        if (!_args.at(ii).has_value()) continue;

        YulString const& arg = *_args.at(ii);
        influences(arg, new_name);
    }

    // Rename returns and influence them.
    for (size_t ii = 0; ii < _callee.m_returns.size(); ii++)
    {
        YulString const& ret_val = _callee.m_returns[ii];

        YulString new_name = state->duplicateVariable(ret_val);
        auto ins = renames.emplace(std::make_pair(ret_val, new_name));
        assertThrow(ins.second, OptimizerException, "duplicate rename");

        YulString const& ret_var = _returns.at(ii);
        influences(new_name, ret_var);
    }

    // Rename and insert the rest of the variables.
    for (auto const& kv: _callee.m_data_flow)
    {
        YulString new_key;
        try
        {
            new_key = renames.at(kv.first);
        }
        catch (std::out_of_range const&)
        {
            new_key = state->duplicateVariable(kv.first);
            renames[kv.first] = new_key;
        }

        for (YulString const& value: kv.second)
        {
            YulString new_value;
            try
            {
                new_value = renames.at(value);
            }
            catch (std::out_of_range const&)
            {
                new_value = state->duplicateVariable(value);
                renames[value] = new_value;
            }

            influences(new_key, new_value);
        }
    }
}

void FunctionScope::propagateTaint()
{
    std::shared_ptr<State> state(m_state.lock());
    std::set<YulString> tainted = state->taintedVariables();

    for (YulString const& t: tainted)
    {
        std::set<YulString> downstream = findDownstream(t);

        for (YulString const& to_taint: downstream)
        {
            state->taintVariable(to_taint);
        }
    }
}

std::set<YulString> FunctionScope::findDownstream(YulString const& _source) const
{
    std::set<YulString> found;
    found.insert(_source);

    std::stack<YulString> to_explore;
    to_explore.push(_source);

    while (!to_explore.empty())
    {
        YulString top = to_explore.top();
        to_explore.pop();

        if (m_data_flow.end() == m_data_flow.find(top))
            continue;

        for (YulString const& name: m_data_flow.at(top))
        {
            if (found.insert(name).second)
            {
                to_explore.push(name);
            }
        }
    }

    return found;
}

void FunctionScope::dump_state() const
{
    std::cout << "\t" << m_name.str() << "(";

    for (auto const& p: m_parameters)
    {
        std::cout << p.str() << ", ";
    }

    std::cout << ") -> ";

    for (auto const& r: m_returns)
    {
        std::cout << r.str() << ", ";
    }

    std::cout << std::endl;

    std::cout << "\t\tData Flow:" << std::endl;
    std::cout
        << "\t\t\t"
        << std::left
        << std::setw(20)
        << "{upstream}"
        << " -> {downstream}"
        << std::endl
        << std::endl;

    for (auto const& kv: m_data_flow)
    {
        std::cout
            << "\t\t\t"
            << std::left
            << std::setw(20)
            << kv.first.str()
            << " -> "
            << std::flush;

        for (YulString const& downstream: kv.second)
        {
            std::cout << downstream.str() << ", ";
        }

        std::cout << std::endl;
    }


    std::cout << "\t\tUnresolved Function Calls:" << std::endl;

    for (auto const& cs: m_unresolved_calls)
    {
        std::cout
            << "\t\t\t- "
            << cs.callee.str()
            << std::endl;
    }
}

void State::verify() const
{
    for (auto const& kv: m_variables)
    {
        if (kv.second.isProtected() && kv.second.virtue() == Virtue::Tainted)
        {
            assertThrow(false, OptimizerException, "tainted variable used");
        }
    }
}

void State::resolve()
{
    std::deque<YulString> unresolved_functions;

    for (auto const& kv: m_functions)
    {
        unresolved_functions.push_back(kv.first);
    }

    while (!unresolved_functions.empty())
    {
        YulString resolving = unresolved_functions.front();
        unresolved_functions.pop_front();

        FunctionScope& fn = m_functions.at(resolving);

        if (!fn.resolve())
        {
            unresolved_functions.push_back(resolving);
        }
    }
}

void State::dump() const
{
    std::cout << "State:" << std::endl;

    std::cout << "\tKnown Variables:" << std::endl;
    for (auto const& kv: m_variables)
    {
        bool untaintable = kv.second.isProtected();

        std::cout
            << "\t\t"
            << std::left
            << std::setw(20)
            << kv.first.str()
            << " ["
            << kv.second.virtue_str()
            << "]";

        if (untaintable)
        {
            std::cout << " [Untaintable]";
        }

        std::cout << std::endl;
    }

    std::cout << std::endl;
    std::cout << "Functions:" << std::endl;

    for (auto const& kv: m_functions)
    {
        kv.second.dump_state();
        std::cout << std::endl;
    }
}
FunctionScope& State::addFunction(FunctionScope scope)
{
    YulString name = scope.name();
    m_functions.emplace(std::make_pair(name, scope));
    return m_functions.at(name);
}

std::shared_ptr<State> State::make_shared(Dialect const& _dialect)
{
    shared_ptr<State> ptr = std::make_shared<State>(State(_dialect));

    // Insert a function scope for code outside of functions.
    FunctionScope main{std::weak_ptr(ptr)};
    ptr->m_functions.emplace(std::make_pair(main.name(), main));

    return ptr;
}


class StateDestroyer: public ASTWalker
{
public:
    StateDestroyer() = delete;
	explicit StateDestroyer(Dialect const& _dialect);

    using ASTWalker::operator();

    void operator()(FunctionDefinition const& _funDef) override;
    void operator()(VariableDeclaration const& _varDef) override;
    void operator()(Assignment const& _assignment) override;

    void dump_state() const;

    void resolve();

    void propagateTaint();
    void verify();

private:
    std::shared_ptr<State> m_state;
    std::stack<FunctionScope> m_func_stack;

    FunctionScope& currentScope();
};

StateDestroyer::StateDestroyer(Dialect const& _dialect)
    : m_state(State::make_shared(_dialect))
{
}

FunctionScope& StateDestroyer::currentScope()
{
    if (m_func_stack.empty())
    {
        return m_state->function(MAIN);
    }
    else
    {
        return m_func_stack.top();
    }
}

void StateDestroyer::verify()
{
    m_state->verify();
}

void StateDestroyer::propagateTaint()
{
    FunctionScope& main = m_state->function(MAIN);
    main.propagateTaint();
}

void StateDestroyer::resolve()
{
    m_state->resolve();
}

void StateDestroyer::operator()(FunctionDefinition const& _funDef)
{
    m_func_stack.emplace(m_state, _funDef);
    (*this)(_funDef.body);

    FunctionScope fn_scope = m_func_stack.top();
    m_func_stack.pop();

    assertThrow(_funDef.name == fn_scope.name(), OptimizerException, "mismatched func");
    m_state->addFunction(fn_scope);
}

void StateDestroyer::operator()(Assignment const& _assignment)
{
    (currentScope())(_assignment);
}

void StateDestroyer::operator()(VariableDeclaration const& _varDef)
{
    (currentScope())(_varDef);
}

void StateDestroyer::dump_state() const
{
    m_state->dump();
}

// EVERYTHING BELOW HERE IS GARBAGE

struct Function
{
    std::vector<YulString> parameters;
    std::vector<YulString> returns;
};

enum class BlockType
{
    Root,
    Function,
    For,
    If,
};

class TaintBlock
{
public:
    TaintBlock() = delete;
    explicit TaintBlock(BlockType bt);

    BlockType type() const { return m_type; }
    YulString const& name() const { return m_name; }

private:
    static unsigned int s_block_count;

    YulString m_name;
    BlockType m_type;
    std::vector<YulString> m_conditions;
};

unsigned int TaintBlock::s_block_count;

TaintBlock::TaintBlock(BlockType bt) : m_type(bt)
{
    std::stringstream ss;
    ss << "!!block_" << s_block_count;
    m_name = YulString(ss.str());

    s_block_count += 1;
}

class Variable;

class Scope
{
public:
    std::set<YulString> find_downstream(YulString const& source) const;

    static Scope join(Scope const& base, Scope const& sub);

	void influences(YulString _upstream, YulString _downstream);
	void influences(Expression const& _upstream, YulString _downstream);
	void dump_state() const;
    std::vector<YulString> find_path(YulString const& source, YulString const& dest) const;

private:
    std::map<YulString, std::set<YulString>> m_graph;
};

Scope Scope::join(Scope const& base, Scope const& sub)
{
    Scope joined;
    joined.m_graph.insert(base.m_graph.begin(), base.m_graph.end());

    for (auto const& kv: sub.m_graph)
    {
        for (YulString const& downstream: kv.second)
        {
            joined.m_graph[kv.first].insert(downstream);
        }
    }

    return joined;
}

void Scope::dump_state() const
{
    std::cout << "Data Flow:" << std::endl;
    std::cout
        << "\t"
        << std::left
        << std::setw(20)
        << "{upstream}"
        << " -> {downstream}"
        << std::endl
        << std::endl;

    for (auto const& kv: m_graph)
    {
        std::cout
            << "\t"
            << std::left
            << std::setw(20)
            << kv.first.str()
            << " -> "
            << std::flush;

        for (YulString const& downstream: kv.second)
        {
            std::cout << downstream.str() << ", ";
        }

        std::cout << std::endl;
    }

}

void Scope::influences(Expression const& _upstream, YulString _downstream)
{
    if (holds_alternative<Literal>(_upstream))
    {
        return;
    }

    assertThrow(holds_alternative<Identifier>(_upstream), OptimizerException, "upstream expr must be literal or identifier");
    Identifier const& upstream_ident = std::get<Identifier>(_upstream);

    influences(upstream_ident.name, _downstream);
}

void Scope::influences(YulString _upstream, YulString _downstream)
{
    m_graph[_upstream].insert(_downstream);
}

std::vector<YulString> Scope::find_path(YulString const& source, YulString const& dest) const
{
    struct Foo
    {
        std::vector<YulString> path;
        YulString next;
    };

    std::set<YulString> found;
    found.insert(source);

    std::stack<Foo> to_explore;

    Foo initial;
    initial.next = source;

    to_explore.push(initial);

    while (!to_explore.empty())
    {
        Foo top = to_explore.top();
        to_explore.pop();

        std::vector<YulString> path(top.path);
        path.push_back(top.next);

        if (m_graph.end() == m_graph.find(top.next))
            continue;

        for (YulString const& name: m_graph.at(top.next))
        {
            if (name == dest)
            {
                return path;
            }

            if (found.insert(name).second)
            {
                Foo next;
                next.next = name;
                next.path = path;

                to_explore.push(next);
            }
        }
    }

    std::vector<YulString> aoeu;
    return aoeu;
}

std::set<YulString> Scope::find_downstream(YulString const& source) const
{
    std::set<YulString> found;
    found.insert(source);

    std::stack<YulString> to_explore;
    to_explore.push(source);

    while (!to_explore.empty())
    {
        YulString top = to_explore.top();
        to_explore.pop();

        if (m_graph.end() == m_graph.find(top))
            continue;

        for (YulString const& name: m_graph.at(top))
        {
            if (found.insert(name).second)
            {
                to_explore.push(name);
            }
        }
    }

    return found;
}


class FunctionSensitivityAnalyzer: public ASTWalker
{
public:
	explicit FunctionSensitivityAnalyzer(Dialect const& _dialect);

    using ASTWalker::operator();

    void operator()(FunctionDefinition const& _funDef) override;
    void operator()(VariableDeclaration const& _variableDeclaration) override;
    void operator()(Assignment const& _assignment) override;
    void operator()(FunctionCall const& _funCall) override;
    void operator()(If const& _if) override;

    void dump_state() const;
    void resolve();
    void taint();
    void verify();

private:
    Dialect const& m_dialect;
    std::map<YulString, Variable> m_variables;
    std::map<YulString, Function> m_functions;

    Scope m_root_scope;

    std::map<YulString, std::vector<CallSite>> m_unresolved_calls;

    std::optional<YulString> m_current_function;
    std::optional<std::vector<YulString>> m_current_assignment;

    std::set<YulString> m_to_taint;

    std::set<YulString> m_untaintable;

    std::vector<Scope> m_function_scopes;

    std::stack<TaintBlock> m_blocks;

    YulString currentCaller();

    void taintScope(Scope const&);
    void visitFunc(FunctionCall const&);
    void visitBuiltin(FunctionCall const&, BuiltinFunctionForEVM const*);

    bool resolveOne(YulString const&);

    void addVariable(YulString _name, Variable _var);
    void addFunction(YulString _name, Function _func);

	void enterFunction(FunctionDefinition const&);
	void leaveFunction(FunctionDefinition const&);

	void enterAssignment(std::vector<YulString>);
	void leaveAssignment(std::vector<YulString> const&);

	void taintVariable(YulString const&);

	void untaintable(Expression const&);
	void untaintable(YulString);

	TaintBlock const& currentBlock() const { return m_blocks.top(); }

	void enterBlock(BlockType type);
	void leaveBlock(BlockType type);

    void printAllPaths(YulString const& src, YulString const& dst) const;
};

FunctionSensitivityAnalyzer::FunctionSensitivityAnalyzer(Dialect const& _dialect): m_dialect(_dialect)
{
    m_blocks.emplace(BlockType::Root);
}

void FunctionSensitivityAnalyzer::untaintable(YulString _name)
{
    m_untaintable.insert(_name);
}

void FunctionSensitivityAnalyzer::untaintable(Expression const& _expr)
{
    if (holds_alternative<Literal>(_expr)) return;
    assertThrow(holds_alternative<Identifier>(_expr), OptimizerException, "untaintable non-ident");

    Identifier const& ident = std::get<Identifier>(_expr);
    untaintable(ident.name);
}

void FunctionSensitivityAnalyzer::taintVariable(YulString const& _name)
{
    m_to_taint.insert(_name);
}

void FunctionSensitivityAnalyzer::verify()
{
    for (YulString const& untaintable: m_untaintable)
    {
        Variable const& var = m_variables.at(untaintable);

        if (var.virtue() == Virtue::Tainted)
        {
            for (YulString const& to_taint: m_to_taint)
            {
                printAllPaths(to_taint, untaintable);
            }
        }

        assertThrow(var.virtue() != Virtue::Tainted, OptimizerException, "tainted variable used");
    }
}

void FunctionSensitivityAnalyzer::taint()
{
    taintScope(m_root_scope);

    for (Scope const& scope: m_function_scopes)
    {
        Scope joined = Scope::join(m_root_scope, scope);
        taintScope(joined);
    }
}

void FunctionSensitivityAnalyzer::taintScope(Scope const& scope)
{
    for (YulString const& name: m_to_taint)
    {
        std::set<YulString> all_downstream = scope.find_downstream(name);

        for (YulString const& downstream: all_downstream)
        {
            m_variables.at(downstream).setTainted();
        }
    }
}

void FunctionSensitivityAnalyzer::resolve()
{
    std::deque<YulString> unresolved_functions;

    for (auto const& kv: m_unresolved_calls)
    {
        unresolved_functions.push_back(kv.first);
    }

    while (!unresolved_functions.empty())
    {
        YulString resolving = unresolved_functions.front();
        unresolved_functions.pop_front();

        if (!resolveOne(resolving))
        {
            unresolved_functions.push_back(resolving);
        }
    }
}

bool FunctionSensitivityAnalyzer::resolveOne(YulString const& _funName)
{
    std::cout << "Resolving: " << _funName.str() << std::endl;
    Scope scope;

    std::vector<CallSite>& callsites = m_unresolved_calls.at(_funName);

    while (!callsites.empty())
    {
        CallSite const& cs = callsites.back();

        if (m_unresolved_calls.end() != m_unresolved_calls.find(cs.callee))
        {
            std::cout << "\tFailed: " << cs.callee.str() << std::endl;

            // Check if the callee function is fully resolved. If not, defer
            // resolving this function.

            // TODO: handle cycles in the call graph.
            return false;
        }

        Function const& callee = m_functions.at(cs.callee);

        //
        // Figure out mapping from callee names to caller names.
        //
        std::map<YulString, std::optional<YulString>> callee2caller;

        for (size_t ii = 0; ii < callee.parameters.size(); ii++)
        {
            callee2caller[callee.parameters[ii]] = cs.arguments.at(ii);
        }

        for (size_t ii = 0; ii < callee.returns.size(); ii++)
        {
            callee2caller[callee.returns[ii]] = cs.returns.at(ii);

            // Mark the caller's return variable as influenced by the callee's
            // variable, so that any taints from inside the callee propagate out.
            scope.influences(callee.returns[ii], cs.returns.at(ii));

            std::cout
                << "\t[RET] "
                << callee.returns[ii].str()
                << " influences "
                << cs.returns.at(ii).str()
                << std::endl;
        }

        assertThrow(
            callee2caller.size() == callee.returns.size() + callee.parameters.size(),
            OptimizerException,
            "blorb"
        );

        //
        // Figure out which return values are influenced by which arguments.
        //
        std::set<YulString> returns_params(callee.returns.begin(), callee.returns.end());

        for (size_t ii = 0; ii < callee.parameters.size(); ii++)
        {
            YulString const& param = callee.parameters.at(ii);
            if (!callee2caller.at(param).has_value())
                continue;   // Was a literal value.

            YulString const& arg = *callee2caller.at(param);

            scope.influences(arg, param);

            std::set<YulString> downstream = m_root_scope.find_downstream(param);
            std::vector<YulString> downstream_returns;
            std::set_intersection(
                downstream.begin(),
                downstream.end(),
                returns_params.begin(),
                returns_params.end(),
                std::back_inserter(downstream_returns)
            );

            for (YulString const& downstream_return: downstream_returns)
            {
                auto const& optret = callee2caller.at(downstream_return);
                assertThrow(optret.has_value(), OptimizerException, "blarp");

                m_root_scope.influences(arg, *optret);
            }
        }

        callsites.pop_back();
    }

    m_function_scopes.push_back(scope);
    m_unresolved_calls.erase(_funName);
    return true;
}

void FunctionSensitivityAnalyzer::dump_state() const
{
    std::cout << "Known Variables:" << std::endl;
    for (auto const& kv: m_variables)
    {
        bool untaintable = m_untaintable.end() != m_untaintable.find(kv.first);

        std::cout
            << "\t"
            << std::left
            << std::setw(20)
            << kv.first.str()
            << " ["
            << kv.second.virtue_str()
            << "]";

        if (untaintable)
        {
            std::cout << " [Untaintable]";
        }

        std::cout << std::endl;
    }

    std::cout << std::endl;
    std::cout << "Known Functions:" << std::endl;

    for (auto const& kv: m_functions)
    {
        std::cout
            << "\t"
            << kv.first.str()
            << "("
            << std::flush;

        for (auto const& param: kv.second.parameters)
        {
            std::cout << param.str() << ", " << std::flush;
        }

        std::cout
            << ") -> "
            << std::flush;

        for (auto const& ret: kv.second.returns)
        {
            std::cout << ret.str() << ", " << std::flush;
        }

        std::cout << std::endl;
    }

    std::cout << std::endl;
    m_root_scope.dump_state();

    for (auto const& fscope: m_function_scopes)
    {
        std::cout << std::endl;
        fscope.dump_state();
    }

    std::cout << std::endl;
    std::cout << "Unresolved Function Calls:" << std::endl;

    for (auto const& kv: m_unresolved_calls)
    {
        std::cout
            << "\t"
            << std::left
            << std::setw(60)
            << kv.first.str()
            << " calls:"
            << std::endl;

        for (CallSite const& cs: kv.second)
        {
            std::cout
                << "\t\t- "
                << cs.callee.str()
                << std::endl;
        }
    }
}

void FunctionSensitivityAnalyzer::printAllPaths(YulString const& src, YulString const& dst) const
{
    auto path = m_root_scope.find_path(src, dst);

    if (!path.empty())
    {
        std::cout << "Path from " << src.str() << " to " << dst.str() << ":" << std::endl;
        std::cout << "\t";

        for (YulString const& foo: path)
        {
            std::cout << foo.str() << " -> ";
        }

        std::cout << dst.str() << std::endl;
    }

    for (Scope const& scope: m_function_scopes)
    {
        Scope merged = Scope::join(m_root_scope, scope);
        auto path = merged.find_path(src, dst);

        if (path.empty()) continue;

        std::cout << "Path from " << src.str() << " to " << dst.str() << ":" << std::endl;
        std::cout << "\t";


        for (YulString const& foo: path)
        {
            std::cout << foo.str() << " -> ";
        }

        std::cout << dst.str() << std::endl;
    }
}

void FunctionSensitivityAnalyzer::enterAssignment(std::vector<YulString> _vars)
{
    assertThrow(!m_current_assignment.has_value(), OptimizerException, "double assign");
    m_current_assignment.emplace(_vars);
}

void FunctionSensitivityAnalyzer::leaveAssignment(std::vector<YulString> const& _vars)
{
    assertThrow(m_current_assignment.has_value(), OptimizerException, "missing assign");
    assertThrow(_vars.size() == m_current_assignment->size(), OptimizerException, "mismatched assign");

    m_current_assignment.reset();
}

void FunctionSensitivityAnalyzer::enterBlock(BlockType type)
{
    YulString const& top = currentBlock().name();
    m_blocks.emplace(type);
    m_root_scope.influences(top, m_blocks.top().name());
    addVariable(currentBlock().name(), Variable(currentBlock().name()));
}

void FunctionSensitivityAnalyzer::leaveBlock(BlockType type)
{
    assertThrow(m_blocks.top().type() == type, OptimizerException, "mismatched block");
    m_blocks.pop();
}

void FunctionSensitivityAnalyzer::enterFunction(FunctionDefinition const& _funDef)
{
    assertThrow(!m_current_function.has_value(), OptimizerException, "double def");
    m_current_function.emplace(_funDef.name);
    enterBlock(BlockType::Function);
    std::cout << currentBlock().name().str() << " is function " << _funDef.name.str() << std::endl;
}

void FunctionSensitivityAnalyzer::leaveFunction(FunctionDefinition const& _funDef)
{
    assertThrow(m_current_function.has_value(), OptimizerException, "missing func");
    assertThrow(_funDef.name == *m_current_function, OptimizerException, "mismatched func");

    m_current_function.reset();
    leaveBlock(BlockType::Function);
}

void FunctionSensitivityAnalyzer::addFunction(YulString _name, Function _func)
{
    auto it = m_functions.find(_name);
    assertThrow(it == m_functions.end(), OptimizerException, "duplicate function");
    m_functions.emplace(std::make_pair(_name, _func));
}

void FunctionSensitivityAnalyzer::addVariable(YulString _name, Variable _var)
{
    auto it = m_variables.find(_name);
    assertThrow(it == m_variables.end(), OptimizerException, "duplicate variable");
    m_variables.emplace(std::make_pair(_name, _var));
}

void FunctionSensitivityAnalyzer::operator()(If const& _if)
{
    const Expression& cond_expr = *_if.condition;
    assertThrow(holds_alternative<Identifier>(cond_expr), OptimizerException, "if with non-identifier");

    const Identifier& cond_ident = std::get<Identifier>(cond_expr);

    enterBlock(BlockType::If);
    m_root_scope.influences(cond_ident.name, currentBlock().name());
    std::cout << currentBlock().name().str() << " is if (" << cond_ident.name.str() << ")" << std::endl;

    (*this)(_if.body);
    leaveBlock(BlockType::If);
}

void FunctionSensitivityAnalyzer::operator()(FunctionDefinition const& _funDef)
{
    std::vector<YulString> params;

    for (TypedName const& tn: _funDef.parameters)
    {
        params.push_back(tn.name);
        addVariable(tn.name, Variable(tn.name));
    }

    std::vector<YulString> returns;

    for (TypedName const& tn: _funDef.returnVariables)
    {
        returns.push_back(tn.name);
        addVariable(tn.name, Variable(tn.name));
    }

    Function fn;
    fn.parameters = params;
    fn.returns = returns;

    addFunction(_funDef.name, fn);

    enterFunction(_funDef);
    (*this)(_funDef.body);
    leaveFunction(_funDef);
}

void FunctionSensitivityAnalyzer::operator()(FunctionCall const& _funCall)
{
    if (EVMDialect const* dialect = dynamic_cast<EVMDialect const*>(&m_dialect))
    {
        if (auto const* builtin = dialect->builtin(_funCall.functionName.name))
        {
            visitBuiltin(_funCall, builtin);
        }
        else
        {
            visitFunc(_funCall);
        }
    }
}

void FunctionSensitivityAnalyzer::visitBuiltin(FunctionCall const& _funCall, BuiltinFunctionForEVM const* _builtin)
{
    if (!_builtin->instruction)
    {
        std::cout << "Builtin with no instruction: " << _funCall.functionName.name.str() << std::endl;
        return;
    }

    std::vector<YulString> returns = m_current_assignment.value_or(std::vector<YulString>());

    switch (*_builtin->instruction)
    {
        case evmasm::Instruction::STOP:
            break;

        case evmasm::Instruction::ADD:
        case evmasm::Instruction::MUL:
        case evmasm::Instruction::SUB:
        case evmasm::Instruction::DIV:
        case evmasm::Instruction::SDIV:
        case evmasm::Instruction::MOD:
        case evmasm::Instruction::SMOD:
        case evmasm::Instruction::EXP:
        case evmasm::Instruction::SIGNEXTEND:
        case evmasm::Instruction::LT:
        case evmasm::Instruction::GT:
        case evmasm::Instruction::SLT:
        case evmasm::Instruction::SGT:
        case evmasm::Instruction::EQ:
        case evmasm::Instruction::AND:
        case evmasm::Instruction::OR:
        case evmasm::Instruction::XOR:
        case evmasm::Instruction::BYTE:
        case evmasm::Instruction::SHL:
        case evmasm::Instruction::SHR:
        case evmasm::Instruction::SAR:
            m_root_scope.influences(_funCall.arguments.at(0), returns.at(0));
            m_root_scope.influences(_funCall.arguments.at(1), returns.at(0));
            break;

        case evmasm::Instruction::ADDMOD:
        case evmasm::Instruction::MULMOD:
            m_root_scope.influences(_funCall.arguments.at(0), returns.at(0));
            m_root_scope.influences(_funCall.arguments.at(1), returns.at(0));
            m_root_scope.influences(_funCall.arguments.at(2), returns.at(0));
            break;

        case evmasm::Instruction::ISZERO:
        case evmasm::Instruction::NOT:
        case evmasm::Instruction::CALLDATALOAD:
        case evmasm::Instruction::BLOCKHASH:
            m_root_scope.influences(_funCall.arguments.at(0), returns.at(0));
            break;

        case evmasm::Instruction::RETURN:
        case evmasm::Instruction::CREATE:
        case evmasm::Instruction::CREATE2:
        case evmasm::Instruction::MLOAD:
        case evmasm::Instruction::MSTORE:
        case evmasm::Instruction::MSTORE8:
        case evmasm::Instruction::RETURNDATACOPY:
        case evmasm::Instruction::EXTCODECOPY:
        case evmasm::Instruction::CODECOPY:
        case evmasm::Instruction::CALLDATACOPY:
        case evmasm::Instruction::KECCAK256:
            std::cout
                << "memory not supported ("
                << _funCall.functionName.name.str()
                << ")"
                << std::endl;
            break;

        case evmasm::Instruction::ADDRESS:
        case evmasm::Instruction::ORIGIN:
        case evmasm::Instruction::CALLER:
        case evmasm::Instruction::CALLVALUE:
        case evmasm::Instruction::CODESIZE:
        case evmasm::Instruction::GASPRICE:
        case evmasm::Instruction::CHAINID:
        case evmasm::Instruction::MSIZE:
            m_variables.at(returns.at(0)).setClean();
            break;

        case evmasm::Instruction::EXTCODEHASH:
        case evmasm::Instruction::EXTCODESIZE:
        case evmasm::Instruction::BALANCE:
            taintVariable(returns.at(0));
            m_root_scope.influences(_funCall.arguments.at(0), returns.at(0));
            untaintable(_funCall.arguments.at(0));
            break;

        case evmasm::Instruction::GAS:
        case evmasm::Instruction::RETURNDATASIZE:
        case evmasm::Instruction::CALLDATASIZE:
        case evmasm::Instruction::COINBASE:
        case evmasm::Instruction::TIMESTAMP:
        case evmasm::Instruction::NUMBER:
        case evmasm::Instruction::DIFFICULTY:
        case evmasm::Instruction::GASLIMIT:
        case evmasm::Instruction::SELFBALANCE:
            taintVariable(returns.at(0));
            break;

        case evmasm::Instruction::JUMPDEST:
            break;

        case evmasm::Instruction::SLOAD:
            std::cout << "SLOAD tainting " << returns.at(0).str() << std::endl;
            taintVariable(returns.at(0));
            m_root_scope.influences(_funCall.arguments.at(0), returns.at(0));
            untaintable(_funCall.arguments.at(0));
            break;

        case evmasm::Instruction::SSTORE:
            untaintable(_funCall.arguments.at(0));
            break;

        case evmasm::Instruction::JUMP:
        case evmasm::Instruction::JUMPI:
        case evmasm::Instruction::PC:
            assertThrow(false, OptimizerException, "$pc access not supported");
            break;

        case evmasm::Instruction::POP:
            std::cout << "pop?" << std::endl;
            // TODO: Stack manipulation isn't supported.
            break;

        case evmasm::Instruction::PUSH1:
        case evmasm::Instruction::PUSH2:
        case evmasm::Instruction::PUSH3:
        case evmasm::Instruction::PUSH4:
        case evmasm::Instruction::PUSH5:
        case evmasm::Instruction::PUSH6:
        case evmasm::Instruction::PUSH7:
        case evmasm::Instruction::PUSH8:
        case evmasm::Instruction::PUSH9:
        case evmasm::Instruction::PUSH10:
        case evmasm::Instruction::PUSH11:
        case evmasm::Instruction::PUSH12:
        case evmasm::Instruction::PUSH13:
        case evmasm::Instruction::PUSH14:
        case evmasm::Instruction::PUSH15:
        case evmasm::Instruction::PUSH16:
        case evmasm::Instruction::PUSH17:
        case evmasm::Instruction::PUSH18:
        case evmasm::Instruction::PUSH19:
        case evmasm::Instruction::PUSH20:
        case evmasm::Instruction::PUSH21:
        case evmasm::Instruction::PUSH22:
        case evmasm::Instruction::PUSH23:
        case evmasm::Instruction::PUSH24:
        case evmasm::Instruction::PUSH25:
        case evmasm::Instruction::PUSH26:
        case evmasm::Instruction::PUSH27:
        case evmasm::Instruction::PUSH28:
        case evmasm::Instruction::PUSH29:
        case evmasm::Instruction::PUSH30:
        case evmasm::Instruction::PUSH31:
        case evmasm::Instruction::PUSH32:

        case evmasm::Instruction::DUP1:
        case evmasm::Instruction::DUP2:
        case evmasm::Instruction::DUP3:
        case evmasm::Instruction::DUP4:
        case evmasm::Instruction::DUP5:
        case evmasm::Instruction::DUP6:
        case evmasm::Instruction::DUP7:
        case evmasm::Instruction::DUP8:
        case evmasm::Instruction::DUP9:
        case evmasm::Instruction::DUP10:
        case evmasm::Instruction::DUP11:
        case evmasm::Instruction::DUP12:
        case evmasm::Instruction::DUP13:
        case evmasm::Instruction::DUP14:
        case evmasm::Instruction::DUP15:
        case evmasm::Instruction::DUP16:

        case evmasm::Instruction::SWAP1:
        case evmasm::Instruction::SWAP2:
        case evmasm::Instruction::SWAP3:
        case evmasm::Instruction::SWAP4:
        case evmasm::Instruction::SWAP5:
        case evmasm::Instruction::SWAP6:
        case evmasm::Instruction::SWAP7:
        case evmasm::Instruction::SWAP8:
        case evmasm::Instruction::SWAP9:
        case evmasm::Instruction::SWAP10:
        case evmasm::Instruction::SWAP11:
        case evmasm::Instruction::SWAP12:
        case evmasm::Instruction::SWAP13:
        case evmasm::Instruction::SWAP14:
        case evmasm::Instruction::SWAP15:
        case evmasm::Instruction::SWAP16:
            assertThrow(false, OptimizerException, "stack not implemented");
            break;

        case evmasm::Instruction::LOG0:
        case evmasm::Instruction::LOG1:
        case evmasm::Instruction::LOG2:
        case evmasm::Instruction::LOG3:
        case evmasm::Instruction::LOG4:
            break;

        case evmasm::Instruction::JUMPTO:
        case evmasm::Instruction::JUMPIF:
        case evmasm::Instruction::JUMPV:
        case evmasm::Instruction::JUMPSUB:
        case evmasm::Instruction::JUMPSUBV:
        case evmasm::Instruction::BEGINSUB:
        case evmasm::Instruction::BEGINDATA:
        case evmasm::Instruction::RETURNSUB:
        case evmasm::Instruction::PUTLOCAL:
        case evmasm::Instruction::GETLOCAL:
            assertThrow(false, OptimizerException, "unknown instruction");
            break;

        case evmasm::Instruction::CALL:
        case evmasm::Instruction::STATICCALL:
        case evmasm::Instruction::CALLCODE:
        case evmasm::Instruction::DELEGATECALL:
            taintVariable(returns.at(0));
            break;

        case evmasm::Instruction::REVERT:
        case evmasm::Instruction::INVALID:
        case evmasm::Instruction::SELFDESTRUCT:
            break;
    }
}

YulString FunctionSensitivityAnalyzer::currentCaller()
{
    YulString caller;

    if (m_current_function.has_value())
    {
        caller = *m_current_function;
    }
    else
    {
        caller = YulString("!!MAIN");
    }

    return caller;
}

void FunctionSensitivityAnalyzer::visitFunc(FunctionCall const& _funCall)
{
    YulString caller = currentCaller();

    std::vector<std::optional<YulString>> args;

    for (Expression const& expr: _funCall.arguments)
    {
        if (holds_alternative<Literal>(expr))
        {
            std::optional<YulString> empty;
            args.push_back(empty);
        }
        else if (holds_alternative<Identifier>(expr))
        {
            Identifier const& ident = std::get<Identifier>(expr);
            args.push_back(ident.name);
        }
        else
        {
            assertThrow(false, OptimizerException, "unexpected function argument");
        }
    }

    std::vector<YulString> returns = m_current_assignment.value_or(std::vector<YulString>());

    CallSite cs;
    cs.callee = _funCall.functionName.name;
    cs.arguments = args;
    cs.returns = returns;

    m_unresolved_calls[caller].push_back(cs);
}

void FunctionSensitivityAnalyzer::operator()(VariableDeclaration const& _variableDeclaration)
{
    for (TypedName const& tn: _variableDeclaration.variables)
    {
        addVariable(tn.name, Variable(tn.name));
    }

	auto const &cb = currentBlock();
	for (TypedName const& v: _variableDeclaration.variables)
    {
        m_root_scope.influences(cb.name(), v.name);
    }

    if (holds_alternative<Identifier>(*_variableDeclaration.value))
    {
        assertThrow(
            1 == _variableDeclaration.variables.size(),
            OptimizerException,
            "not enough variables to unpack (expected 1)"
        );

        Identifier const& ident = std::get<Identifier>(*_variableDeclaration.value);

		m_root_scope.influences(ident.name, _variableDeclaration.variables[0].name);
	}
	else if (holds_alternative<Literal>(*_variableDeclaration.value))
    {
        assertThrow(
            1 == _variableDeclaration.variables.size(),
            OptimizerException,
            "not enough variables to unpack (expected 1)"
        );

        m_variables.at(_variableDeclaration.variables[0].name).setClean();
    }
    else if (holds_alternative<FunctionCall>(*_variableDeclaration.value))
    {
        FunctionCall const& call = std::get<FunctionCall>(*_variableDeclaration.value);

        std::vector<YulString> vars;
        for (TypedName const& tn: _variableDeclaration.variables)
        {
            vars.push_back(tn.name);
        }

        enterAssignment(vars);
        (*this)(call);
        leaveAssignment(vars);
    }
    else
    {
        assertThrow(false, OptimizerException, "unexpected declaration value");
    }
}

void FunctionSensitivityAnalyzer::operator()(Assignment const& _assignment)
{
	auto const &cb = currentBlock();
	for (Identifier const& v: _assignment.variableNames)
    {
        m_root_scope.influences(cb.name(), v.name);
    }

    if (holds_alternative<Identifier>(*_assignment.value))
    {
        assertThrow(
            1 == _assignment.variableNames.size(),
            OptimizerException,
            "not enough variables to unpack (expected 1)"
        );

        Identifier const& ident = std::get<Identifier>(*_assignment.value);

		m_root_scope.influences(ident.name, _assignment.variableNames[0].name);
	}
	else if (holds_alternative<Literal>(*_assignment.value))
    {
        assertThrow(
            1 == _assignment.variableNames.size(),
            OptimizerException,
            "not enough variables to unpack (expected 1)"
        );

        m_variables.at(_assignment.variableNames[0].name).setClean();
    }
    else if (holds_alternative<FunctionCall>(*_assignment.value))
    {
        FunctionCall const& call = std::get<FunctionCall>(*_assignment.value);

        std::vector<YulString> vars;
        for (Identifier const& ident: _assignment.variableNames)
        {
            vars.push_back(ident.name);
        }

        enterAssignment(vars);
        (*this)(call);
        leaveAssignment(vars);
    }
    else
    {
        assertThrow(false, OptimizerException, "unexpected declaration value");
    }
}

void OrderDependentStateDestroyer::run(OptimiserStepContext& _context, Block& _ast)
{
    std::cout << yul::AsmPrinter()(_ast) << std::endl;

    StateDestroyer sd(_context.dialect);
    (sd)(_ast);
    sd.resolve();
    sd.propagateTaint();
    sd.dump_state();
    sd.verify();
}
