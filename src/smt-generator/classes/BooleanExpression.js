const comparisonList = require('../../util/comparisons.json');

function findComparison(comparison) {
	let result = comparison;

	comparisonList.map((c) => {
		if (comparison === c.symbol) {
			result = c.smtSymbol ? c.smtSymbol : c.symbol;
		}
	});

	return result;
}

module.exports = class SmtBooleanExpression {
	constructor(comparison, args, isInverted) {
		if (!comparison) {
			throw new Error('Argument "comparison" is required.');
		}

		if (!Array.isArray(args)) {
			throw new Error('Expected argument "args" to be Array.');
		}

		this.comparison = findComparison(comparison);
		this.args = args;
		this.isInverted = typeof isInverted === 'boolean' ? isInverted : false;
	}

	setInverted(value) {
		this.isInverted = value;
	}

	toString() {
		const args = this.args.map((a) => {
			return a.toString();
		}).join(' ');
		const command = `(${this.comparison} ${args})`;

		return this.isInverted ? `(not ${command})` : command;
	}
};
