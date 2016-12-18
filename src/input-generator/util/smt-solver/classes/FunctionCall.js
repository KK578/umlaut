module.exports = class SmtDeclareFunction {
	constructor(name, args) {
		if (!name) {
			throw new Error('Argument "name" is required.');
		}

		if (!Array.isArray(args)) {
			args = [];
		}

		this.name = name;
		this.args = args;
	}

	toString() {
		if (this.args.length > 0) {
			const args = this.args.join(' ');

			return `(${this.name} ${args})`;
		}
		else {
			return `(${this.name})`;
		}
	}
};
