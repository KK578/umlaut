module.exports = class SmtDeclareFunction {
	constructor(name, args) {
		this.name = name;
		this.args = args;
	}

	toString() {
		const args = this.args.join(' ');

		return `(${this.name} ${args})`;
	}
};
