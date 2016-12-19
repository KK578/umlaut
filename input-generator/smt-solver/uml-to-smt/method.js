const Smt = require('../../util/smt-solver/classes.js');

function convertType(type) {
	switch (type) {
		case 'Integer':
			return 'Int';
	}
}

class SmtMethod {
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
		args.map((a) => {
			const type = convertType(a.type);
			const command = new Smt.DeclareConst(a.name, type);

			// Note the existence of the argument to the class for get-value calls later.
			if (!this.constants[a.name]) {
				this.constants[a.name] = true;
			}

			this.commands.push(command);
		});
	}

	declareFunction(method) {
		// Declare the function to SMT.
		const type = convertType(method.returnType.type);
		const args = method.arguments.map((a) => {
			return convertType(a.type);
		});
		const command = new Smt.DeclareFunction(method.name, type, args);

		this.commands.push(command);
	}

	allValidConditions(method) {
		// Add a layer to the stack so we can pop later and keep the declarations.
		this.commands.push(new Smt.Echo('-----Valid'));
		this.commands.push(new Smt.StackModifier('push'));

		// For each precondition, add it to the stack.
		method.preconditions.map((c) => {
			const conditionCommand = new Smt.BooleanExpression(c.comparison, c.arguments);

			this.commands.push(new Smt.Assertion(conditionCommand));
		});

		// Declare a variable for the result
		if (method.returnType.type !== 'void') {
			const resultType = convertType(method.returnType.type);
			const resultDeclare = new Smt.DeclareConst('result', resultType);

			const functionArgs = method.arguments.map((a) => {
				return a.name;
			});
			const functionCall = new Smt.FunctionCall(method.name, functionArgs);
			const resultAssert = new Smt.Assertion(
				new Smt.BooleanExpression('=', ['result', functionCall])
			);

			this.commands.push(resultDeclare);
			this.commands.push(resultAssert);
		}

		// Add postconditions so that the inputs may be more interesting.
		method.postconditions.map((c) => {
			const conditionCommand = new Smt.BooleanExpression(c.comparison, c.arguments);

			this.commands.push(new Smt.Assertion(conditionCommand));
		});

		// Check satisfiability and get values of arguments.
		this.commands.push(new Smt.GetValue(this.getConstants()));
		this.commands.push(new Smt.StackModifier('pop'));
	}

	singularInvalidConditions(method) {
		method.preconditions.map((a, i) => {
			// For each precondition, add it to the stack.
			this.commands.push(new Smt.Echo(`-----Complement ${a.id}`));
			this.commands.push(new Smt.StackModifier('push'));

			method.preconditions.map((c, j) => {
				const expression = new Smt.BooleanExpression(c.comparison, c.arguments);

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
}

module.exports = SmtMethod;
