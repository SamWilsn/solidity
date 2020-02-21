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
 * Optimiser component that explodes if a state access (sload / sstore) depends
 * on another state access.
 */

#pragma once

#include <libyul/YulString.h>
#include <libyul/AsmDataForward.h>
#include <libyul/optimiser/ASTWalker.h>
#include <libyul/optimiser/OptimiserStep.h>

#include <map>
#include <stack>
#include <tuple>
#include <vector>

namespace yul
{

class ZeroRetVar: public ASTModifier
{
public:
	static constexpr char const* name{"ZeroRetVar"};
	static void run(::yul::OptimiserStepContext&, ::yul::Block& _ast);

	ZeroRetVar() = default;
	ZeroRetVar(ZeroRetVar const&) = delete;
	ZeroRetVar& operator=(ZeroRetVar const&) = delete;
	ZeroRetVar(ZeroRetVar&&) = default;

	using ASTModifier::operator();

	void operator()(FunctionDefinition&) override;
	void operator()(Assignment&) override;
	void operator()(VariableDeclaration&) override;
	void operator()(FunctionCall&) override;
private:
	unsigned int m_count = 0;

	std::set<YulString> m_unassigned_returns;
	YulString m_zero;
};

}
