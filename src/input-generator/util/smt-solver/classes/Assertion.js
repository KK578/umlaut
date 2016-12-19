module.exports = class SmtAssertion {
	constructor(expression) {
		if (!expression) {
			throw new Error('Argument "expression" is required.');
		}

		this.expression = expression;
	}

	toString() {
		const expression = this.expression.toString();

		return `(assert ${expression})`;
	}
};
