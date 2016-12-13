module.exports = class SmtModel {
	constructor(args) {
		this.args = args;
	}

	toString() {
		const args = this.args.join(' ');
		const satCommand = '(check-sat)';
		const getCommand = `(get-value (${args}))`;

		return `${satCommand}\n${getCommand}`;
	}
};
