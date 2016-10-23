const util = require('../util/smt-util.js');

module.exports = class SmtDeclareFunction {
	constructor(name, type, args) {
		this.name = util.validateName(name);
		this.type = util.validateType(type);
		this.args = args.map((a) => {
			return util.validateType(a);
		});
	}

	toString() {
		const args = this.args.join(' ');

		return `(declare-fun ${this.name} (${args}) ${this.type})`;
	}
};
