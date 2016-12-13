module.exports = class SmtDeclareFunction {
	constructor(name, type, args) {
		this.name = name;
		this.type = type;
		this.args = args;
	}

	toString() {
		const args = this.args.join(' ');

		return `(declare-fun ${this.name} (${args}) ${this.type})`;
	}
};
