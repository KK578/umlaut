module.exports = class SmtDeclareFunction {
	constructor(expression) {
		this.expression = expression;
	}

	toString() {
		const expression = this.expression.toString();

		return `(assert ${expression})`;
	}
};
