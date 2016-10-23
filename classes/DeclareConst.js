module.exports = class SmtDeclareConst {
	constructor(name, type) {
		this.name = name;
		this.type = type;
	}

	toString() {
		return `(declare-const ${this.name} ${this.type})`;
	}
};
