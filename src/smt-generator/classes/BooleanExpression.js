module.exports = class SmtBooleanExpression {
	constructor(comparison, args) {
		this.comparison = comparison;
		this.args = args;
		this.isInverted = false;
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