const util = require('../util/smt-util.js');

module.exports = class SmtBooleanExpression {
	constructor(comparison, args) {
		this.comparison = util.validateComparison(comparison);
		this.isInverted = /!/.test(comparison);

		this.args = args.map((a) => {
			return util.validateType(a);
		});
	}

	setInverted(value) {
		this.isInverted = value;
	}

	toString() {
		const args = this.args.map((a) => {
			return a.toString();
		}).join(' ');
		const command = `(${comparison} ${args})`;

		return this.isInverted ? `(not ${command})` : command;
	}
};
