module.exports = class SmtEcho {
	constructor(output) {
		this.output = output;
	}

	toString() {
		const output = this.output.replace(/"/g, '""');

		return `(echo "${output}")`;
	}
};
