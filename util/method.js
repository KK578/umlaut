const SMT = new require('./smt-classes.js');

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
			const command = SMT.DeclareConst(a);

			// Note the existence of the argument to the class for get-value calls later.
			if (!this.constants[a.name]) {
				this.constants[a.name] = true;
			}

			this.commands.push(command);
		});
	}

	declareFunction(method) {
		// Declare the function to SMT.
		const command = SMT.DeclareFunction(method);

		this.commands.push(command);
	}

	allValidConditions(method) {
		// Add a layer to the stack so we can pop later and keep the declarations.
		this.commands.push(SMT.StackPush());

		// For each precondition, add it to the stack.
		method.preconditions.map((c) => {
			const command = SMT.Assertion(c);

			this.commands.push(command);
		});

		// Declare a variable for the result
		if (method.return.type !== 'void') {
			const resultDeclare = SMT.DeclareConst({ name: 'result', type: method.return.type });
			const functionCall = SMT.FunctionCall(method);
			const resultAssert = SMT.Assertion({
				comparison: '=',
				arguments: [
					'result',
					functionCall
				]
			});

			this.commands.push(resultDeclare);
			this.commands.push(resultAssert);
		}

		// Add postconditions so that the inputs may be more interesting.
		method.postconditions.map((c) => {
			const command = SMT.Assertion(c);

			this.commands.push(command);
		});

		// Check satisfiability and get values of arguments.
		this.commands.push(SMT.GetValues(this.getConstants()));
		this.commands.push(SMT.StackPop());
	}

	singularInvalidConditions(method) {
		// For each precondition, invert the result and get the values to use as inputs.
		method.preconditions.map((c) => {
			this.commands.push(SMT.StackPush());

			const expression = SMT.BooleanExpression(c);
			expression.setInverted(!expression.isInverted);

			const command = SMT.Assertion(expression);
			this.commands.push(command);

			this.commands.push(SMT.GetValues(this.getConstants()));
			this.commands.push(SMT.StackPop());
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
