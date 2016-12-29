module.exports = class SmtDeclareFunction {
	constructor(name, type, args) {
		if (!name) {
			throw new Error('Argument "name" is required.');
		}

		if (!type) {
			throw new Error('Argument "type" is required.');
		}

		if (!Array.isArray(args)) {
			throw new Error('Expected argument "args" to be Array.');
		}

		this.name = name;
		this.type = type;
		this.args = args;
	}

	toString() {
		const args = this.args.join(' ');

		return `(declare-fun ${this.name} (${args}) ${this.type})`;
	}
};
