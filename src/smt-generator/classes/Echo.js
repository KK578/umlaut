module.exports = class SmtEcho {
	constructor(output) {
		if (!output) {
			output = "";
		}

		this.output = output;
	}

	toString() {
		const output = this.output.replace(/"/g, '""');

		return `(echo "${output}")`;
	}
};
