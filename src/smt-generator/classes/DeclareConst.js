module.exports = class SmtDeclareConst {
	constructor(name, type) {
		if (!name) {
			throw new Error('Argument "name" is required.');
		}

		if (!type) {
			throw new Error('Argument "type" is required.');
		}

		this.name = name;
		this.type = type;
	}

	toString() {
		return `(declare-const ${this.name} ${this.type})`;
	}
};
