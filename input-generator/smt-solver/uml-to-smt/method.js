const Smt = require('../util/classes.js');
const comparisons = require('../../../util/comparisons.js');

function convertType(type) {
	switch (type) {
		case 'Integer':
			return 'Int';

		default:
			return type;
	}
}

module.exports = class SmtMethod {
	constructor(method) {
		this.commands = [];
		this.constants = [];

		this.declareArguments(method.arguments);
		this.declareFunction(method);
		this.allValidConditions(method);
		this.singularInvalidConditions(method);
	}

	declareArguments(args) {
		// For every argument to the function, add a declaration to SMT.
		Object.keys(args).map((name) => {
			const type = convertType(args[name]);
			const command = new Smt.DeclareConst(name, type);

			// Note the existence of the argument to the class for get-value calls later.
			if (!this.constants[name]) {
				this.constants[name] = true;
			}

			this.commands.push(command);
		});
	}

	declareFunction(method) {
		// Declare the function to SMT.
		const type = convertType(method.type);
		const args = Object.keys(method.arguments).map((t) => {
			return convertType(method.arguments[t]);
		});
		const command = new Smt.DeclareFunction(method.name, type, args);

		this.commands.push(command);
	}

	allValidConditions(method) {
		// Add a layer to the stack so we can pop later and keep the declarations.
		this.commands.push(new Smt.Echo('[[Valid]]'));
		this.commands.push(new Smt.StackModifier('push'));

		// For each precondition, add it to the stack.
		method.preconditions.map((c) => {
			const comparison = comparisons.toSmtSymbol(c.comparison);
			const conditionCommand = new Smt.BooleanExpression(comparison, c.arguments);

			this.commands.push(new Smt.Assertion(conditionCommand));
		});

		// Declare a variable for the result
		if (method.type !== 'void') {
			const resultType = convertType(method.type);
			const resultDeclare = new Smt.DeclareConst('result', resultType);

			const functionArgs = Object.keys(method.arguments);
			const functionCall = new Smt.FunctionCall(method.name, functionArgs);
			const resultAssert = new Smt.Assertion(
				new Smt.BooleanExpression('=', ['result', functionCall])
			);

			this.commands.push(resultDeclare);
			this.commands.push(resultAssert);
		}

		// Add postconditions so that the inputs may be more interesting.
		method.postconditions.map((c) => {
			const comparison = comparisons.toSmtSymbol(c.comparison);
			const conditionCommand = new Smt.BooleanExpression(comparison, c.arguments);

			this.commands.push(new Smt.Assertion(conditionCommand));
		});

		// Check satisfiability and get values of arguments.
		this.commands.push(new Smt.GetValue(this.getConstants()));
		this.commands.push(new Smt.StackModifier('pop'));
	}

	singularInvalidConditions(method) {
		method.preconditions.map((a, i) => {
			// For each precondition, add it to the stack.
			this.commands.push(new Smt.Echo(`~~[[${a.id}]]`));
			this.commands.push(new Smt.StackModifier('push'));

			method.preconditions.map((c, j) => {
				const comparison = comparisons.toSmtSymbol(c.comparison);
				const expression = new Smt.BooleanExpression(comparison, c.arguments);

				// If it is the one that we are testing,
				//  invert the result and get the values to use as inputs.
				if (i === j) {
					expression.setInverted(!expression.isInverted);
				}

				this.commands.push(new Smt.Assertion(expression));
			});

			this.commands.push(new Smt.GetValue(this.getConstants()));
			this.commands.push(new Smt.StackModifier('pop'));
		});
	}

	getConstants() {
		return Object.keys(this.constants);
	}

	getCommands() {
		return this.commands;
	}
};
