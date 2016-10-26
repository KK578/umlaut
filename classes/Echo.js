module.exports = class SmtEcho {
	constructor(output) {
		this.output = output;
	}

	toString() {
		var output = this.output.replace(/"/g, '""');

		return `(echo "${output}")`;
	}
};
