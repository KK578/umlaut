const test = {
	name: 'Add',
	arguments: [
		{
			name: "a",
			type: "Int"
		},
		{
			name: "b",
			type: "Int"
		}
	],
	return: { type: "Int" },
	preconditions: [
		{
			type: ">=",
			left: "a",
			right: "0"
		},
		{
			type: ">=",
			left: "b",
			right: "0"
		}
	],
	postconditions: [
		{
			type: ">=",
			left: "result",
			right: "a"
		}
	]
};

/* 1) Declare arguments
 * 2) Declare function
 * 3) Push to stack
 * 4) Declare all pre and post conditions
 * 5) Get values
 * 6) Pop stack
 * 7) For each precondition
 *    a) Invert
 *    b) Declare condition
 *    c) Get values
 * 8)
*/

const smtStringsSource = require('./smt-strings.js');
const smtStrings = new smtStringsSource();

class SmtMethod {
	constructor(method) {
		this.smtCommands = [];
		this.constants = [];

		this.declareArguments(method.arguments);
		this.declareFunction(method);
		this.allValidConditions(method);
		this.singularInvalidConditions(method);
	}

	declareArguments(args) {
		// For every argument to the function, add a declaration to SMT.
		args.map((a) => {
			const command = smtStrings.declareConst(a.name, a.type);

			// Note the existence of the argument to the class for get-value calls later.
			if (!this.constants[a.name]) {
				this.constants[a.name] = true;
			}

			this.smtCommands.push(command);
		});
	}

	declareFunction(method) {
		// Declare the function to SMT.
		const args = method.arguments.map((a) => {
			return a.type;
		});
		const type = typeof method.return === 'string' ? method.return : method.return.type;
		const command = smtStrings.declareFunction(method.name, args, type);

		this.smtCommands.push(command);
	}

	allValidConditions(method) {
		// Add a layer to the stack so we can pop later and keep the declarations.
		this.smtCommands.push(smtStrings.stackPush());

		// For each precondition, add it to the stack.
		method.preconditions.map((c) => {
			const command = smtStrings.makeAssertion(c.type, c.left, c.right);

			this.smtCommands.push(command);
		});

		// Add postconditions so that the inputs may be more interesting.
		method.postconditions.map((c) => {
			const args = method.arguments.map((a) => {
				return a.name;
			});

			// HACK: Currently just replace 'result' with the function call.
			const functionCall = smtStrings.makeFunctionCall(method.name, args);
			let left = c.left === 'result' ? functionCall : c.left;
			let right = c.right === 'result' ? functionCall : c.right;

			const command = smtStrings.makeAssertion(c.type, left, right);

			this.smtCommands.push(command);
		});

		// Check satisfiability and get values of arguments.
		this.smtCommands.push(smtStrings.checkSat());
		this.smtCommands.push(smtStrings.getValues(this.getConstants()));
		this.smtCommands.push(smtStrings.stackPop());
	}

	singularInvalidConditions(method) {
		// For each precondition, invert the result and get the values to use as inputs.
		method.preconditions.map((c) => {
			this.smtCommands.push(smtStrings.stackPush());

			const command = smtStrings.makeInvertedAssertion(c.type, c.left, c.right);

			this.smtCommands.push(command);

			this.smtCommands.push(smtStrings.checkSat());
			this.smtCommands.push(smtStrings.getValues(this.getConstants()));
			this.smtCommands.push(smtStrings.stackPop());
		});
	}

	getConstants() {
		return Object.keys(this.constants);
	}

	getCommands() {
		return this.smtCommands;
	}
}

module.exports = {
	class: SmtMethod,
	test
}
