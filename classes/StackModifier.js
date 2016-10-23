module.exports = class SmtStackModifier {
	constructor(mode) {
		this.mode = mode;
	}

	toString() {
		return `(${this.mode})`;
	}
};
