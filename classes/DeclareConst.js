const util = require('../util/smt-util.js');

module.exports = class SmtDeclareConst {
	constructor(name, type) {
		this.name = util.validateName(name);
		this.type = util.validateType(type);
	}

	toString() {
		return `(declare-const ${this.name} ${this.type})`;
	}
};
