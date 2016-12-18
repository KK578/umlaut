module.exports = class SmtModel {
	constructor(args) {
		if (!Array.isArray(args)) {
			throw new Error('Expected argument "args" to be Array.');
		}

		this.args = args;
	}

	toString() {
		const args = this.args.join(' ');
		const satCommand = '(check-sat)';
		const getCommand = `(get-value (${args}))`;

		return `${satCommand}\n${getCommand}`;
	}
};
