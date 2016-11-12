const smt = require('./smt-classes.js');

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
			const command = smt.declareConst(a);

			// Note the existence of the argument to the class for get-value calls later.
			if (!this.constants[a.name]) {
				this.constants[a.name] = true;
			}

			this.commands.push(command);
		});
	}

	declareFunction(method) {
		// Declare the function to SMT.
		const command = smt.declareFunction(method);

		this.commands.push(command);
	}

	allValidConditions(method) {
		// Add a layer to the stack so we can pop later and keep the declarations.
		this.commands.push(smt.echo('-----Valid'));
		this.commands.push(smt.stackPush());

		// For each precondition, add it to the stack.
		method.preconditions.map((c) => {
			const command = smt.assertion(c);

			this.commands.push(command);
		});

		// Declare a variable for the result
		if (method.return.type !== 'void') {
			const resultDeclare = smt.declareConst({ name: 'result', type: method.return.type });
			const functionCall = smt.functionCall(method);
			const resultAssert = smt.assertion({
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
			const command = smt.assertion(c);

			this.commands.push(command);
		});

		// Check satisfiability and get values of arguments.
		this.commands.push(smt.getValues(this.getConstants()));
		this.commands.push(smt.stackPop());
	}

	singularInvalidConditions(method) {
		method.preconditions.map((a, i) => {
			// For each precondition, add it to the stack.
			const inverted = smt.booleanExpression(a);

			this.commands.push(smt.echo(`-----Complement ${inverted.toString()}`));
			this.commands.push(smt.stackPush());

			method.preconditions.map((c, j) => {
				const expression = smt.booleanExpression(c);

				// If it is the one that we are testing,
				//  invert the result and get the values to use as inputs.
				if (i === j) {
					expression.setInverted(!expression.isInverted);
				}

				const command = smt.assertion(expression);
				this.commands.push(command);
			});

			this.commands.push(smt.getValues(this.getConstants()));
			this.commands.push(smt.stackPop());
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
