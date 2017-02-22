const SmtFunctionCall = require('./FunctionCall');
const comparisons = require('../../../../util/comparisons.js');

module.exports = class SmtBooleanExpression {
	constructor(comparison, args, isInverted) {
		if (!comparison) {
			throw new Error('Argument "comparison" is required.');
		}

		if (!Array.isArray(args)) {
			throw new Error('Expected argument "args" to be Array.');
		}

		if (!comparisons.verifySmtSymbol(comparison)) {
			throw new Error(`Comparison "${comparison}" is not a valid SMT comparison.`);
		}

		this.comparison = comparison;
		this.args = args;
		this.isInverted = typeof isInverted === 'boolean' ? isInverted : false;
	}

	setInverted(value) {
		this.isInverted = value;
	}

	toString() {
		const args = this.args.map((a) => {
			if (typeof a === 'object') {
				if (a.label === 'FunctionCall') {
					const fArgs = a.arguments.map((t) => {
						return t.value;
					});
					const functionCommand = new SmtFunctionCall(a.name, fArgs);

					return functionCommand.toString();
				}
			}

			return a.toString();
		}).join(' ');
		const command = `(${this.comparison} ${args})`;

		return this.isInverted ? `(not ${command})` : command;
	}
};
