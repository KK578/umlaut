module.exports = class SmtGetValue {
	constructor(args) {
		if (!Array.isArray(args)) {
			throw new Error('Expected argument "args" to be Array.');
		}

		this.args = args;
	}

	toString() {
		const args = this.args.join(' ');
		const checkSatCommand = '(check-sat)';
		const getValueCommand = `(get-value (${args}))`;

		return `${checkSatCommand}\n${getValueCommand}`;
	}
};
