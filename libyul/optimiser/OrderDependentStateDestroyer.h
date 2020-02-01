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
#include <libyul/backends/evm/EVMDialect.h>

#include <map>
#include <stack>
#include <tuple>
#include <vector>

namespace solidity::yul
{

class OrderDependentStateDestroyer: public ASTWalker
{
public:
	static constexpr char const* name{"OrderDependentStateDestroyer"};
	static void run(OptimiserStepContext&, Block& _ast);

	explicit OrderDependentStateDestroyer(Dialect const& _dialect): m_dialect(_dialect) {}
	OrderDependentStateDestroyer() = delete;
	OrderDependentStateDestroyer(OrderDependentStateDestroyer const&) = delete;
	OrderDependentStateDestroyer& operator=(OrderDependentStateDestroyer const&) = delete;
	OrderDependentStateDestroyer(OrderDependentStateDestroyer&&) = default;

	using ASTWalker::operator();

	void operator()(Assignment const& _assignment) override;
	void operator()(VariableDeclaration const& _variableDeclaration) override;
	void operator()(FunctionCall const& _funCall) override;
	void operator()(FunctionDefinition const& _funDef) override;

private:
	struct FnCall
	{
		YulString name;
		std::vector<YulString> params;
	};

	class Var
	{
	public:
		enum Virtue { Clean = 0, Undecided, Tainted };

		bool sensitive = false;

		Var(Virtue _value = Undecided): m_virtue(_value) {}

		inline void join(Var const& _b)
		{
			// Using "max" works here because of the order of the values in the enum.
			m_virtue =  Virtue(std::max(int(m_virtue), int(_b.m_virtue)));

			m_args.insert(m_args.end(),_b.m_args.begin(),_b.m_args.end());
		}

		inline const char* virtue_str() const {
			switch (m_virtue)
			{
				case Clean:
					return "Clean";
				case Undecided:
					return "Undecided";
				case Tainted:
					return "Tainted";
				default:
					return "";
			}
		}

		inline std::vector<YulString> const& args() const {
			return m_args;
		}

		inline void add_arg(YulString name)
		{
			m_args.push_back(name);
		}

		inline Virtue virtue() const
		{
			return m_virtue;
		}

		inline void undecide()
		{
			// Using "max" works here because of the order of the values in the enum.
			m_virtue =  Virtue(std::max(int(m_virtue), int(Undecided)));
		}

		inline void taint()
		{
			m_virtue = Tainted;
		}
	private:
		Virtue m_virtue = Undecided;
		std::vector<YulString> m_args;
	};

	Dialect const& m_dialect;
	std::map<YulString, Var> m_variables;
	std::map<YulString, std::vector<YulString>> m_functions;
	std::stack<Var, std::vector<Var>> m_stack;
	std::vector<FnCall> m_callsites;

	void visitBuiltin(FunctionCall const& _funCall, BuiltinFunctionForEVM const* builtn);
	void visitFunc(FunctionCall const& _funCall);
	void checkStateAccess(FunctionCall const& _funCall);
	void newVar(YulString const& name, Var v);
};

}
