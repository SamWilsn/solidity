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

#include <libyul/AsmData.h>
#include "libdevcore/Assertions.h"
#include "libyul/AsmDataForward.h"
#include "libyul/Exceptions.h"
#include <libyul/YulString.h>
#include <libyul/optimiser/ASTWalker.h>
#include <libyul/optimiser/ZeroRetVar.h>

#include <memory>
#include <variant>

#include <boost/range/adaptor/reversed.hpp>

using namespace std;
using namespace yul;

void ZeroRetVar::run(OptimiserStepContext&, Block& _ast)
{
    ZeroRetVar zrv;
    zrv(_ast);
}

void ZeroRetVar::operator()(FunctionDefinition& _funDef)
{
    std::stringstream ss;
    ss << "_zero_" << m_count++;
    YulString yname(ss.str());

    m_zero = yname;
    m_unassigned_returns.clear();

    for (TypedName const& ret: _funDef.returnVariables)
    {
        m_unassigned_returns.insert(ret.name);
    }

    if (!_funDef.body.statements.empty())
    {
        Literal zero;
        zero.value = YulString("0");
        zero.kind = LiteralKind::Number;
        zero.location = _funDef.body.location;

        TypedName variable;
        variable.location = _funDef.body.location;
        variable.name = yname;

        vector<Statement>& statements = _funDef.body.statements;
        statements.emplace(statements.begin());

        VariableDeclaration& decl = statements.at(0).emplace<VariableDeclaration>();
        decl.location = _funDef.body.location;
        decl.value = std::make_unique<Expression>(zero);
        decl.variables.push_back(variable);
    }

	(*this)(_funDef.body);
}

void ZeroRetVar::operator()(Assignment& _assign)
{
    for (Identifier const& assignee: _assign.variableNames)
    {
        m_unassigned_returns.erase(assignee.name);
    }

	for (auto& name: _assign.variableNames)
    {
		(*this)(name);
    }

    if (holds_alternative<Identifier>(*_assign.value))
    {
        bool is_zero = false;
        langutil::SourceLocation location;

        {
            Identifier const& value = std::get<Identifier>(*_assign.value);
            is_zero = m_unassigned_returns.find(value.name) != m_unassigned_returns.end();
            location = value.location;
        }

        if (is_zero)
        {
            Identifier& ident = _assign.value->emplace<Identifier>();
            ident.location = location;
            ident.name = m_zero;
        }
    }

	visit(*_assign.value);
}

void ZeroRetVar::operator()(VariableDeclaration& _varDecl)
{
    for (TypedName const& assignee: _varDecl.variables)
    {
        bool contains = m_unassigned_returns.find(assignee.name) == m_unassigned_returns.end();

        assertThrow(contains, OptimizerException, "redefined return variable");
    }

    if (!_varDecl.value)
    {
        return;
    }

    if (holds_alternative<Identifier>(*_varDecl.value))
    {
        bool is_zero = false;
        langutil::SourceLocation location;

        {
            Identifier const& value = std::get<Identifier>(*_varDecl.value);
            is_zero = m_unassigned_returns.find(value.name) != m_unassigned_returns.end();
            location = value.location;
        }

        if (is_zero)
        {
            Identifier& ident = _varDecl.value->emplace<Identifier>();
            ident.location = location;
            ident.name = m_zero;
        }
    }

    visit(*_varDecl.value);
}

void ZeroRetVar::operator()(FunctionCall& _funCall)
{
	for (Expression& arg: _funCall.arguments)
    {
        if (!holds_alternative<Identifier>(arg)) continue;

        bool is_zero = false;
        langutil::SourceLocation location;

        {
            Identifier const& value = std::get<Identifier>(arg);
            is_zero = m_unassigned_returns.find(value.name) != m_unassigned_returns.end();
            location = value.location;
        }

        if (is_zero)
        {
            Identifier& ident = arg.emplace<Identifier>();
            ident.location = location;
            ident.name = m_zero;
        }
    }

	walkVector(_funCall.arguments | boost::adaptors::reversed);
}
