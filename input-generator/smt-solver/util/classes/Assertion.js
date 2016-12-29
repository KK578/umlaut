const SmtBooleanExpression = require('./BooleanExpression');

module.exports = class SmtAssertion {
	constructor(expression) {
		if (!expression) {
			throw new Error('Argument "expression" is required.');
		}

		if (!(expression instanceof SmtBooleanExpression)) {
			throw new Error('Expected "expression" to be a SmtBooleanExpression');
		}

		this.expression = expression;
	}

	toString() {
		const expression = this.expression.toString();

		return `(assert ${expression})`;
	}
};
