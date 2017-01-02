const uuid = require('uuid/v4');
const OclCondition = require('./OclCondition.js');

module.exports = class AnnotatedUmlMethod {
	constructor(name, type, args) {
		if (!name) {
			throw new Error('Argument "name" is required.');
		}

		if (!type) {
			throw new Error('Argument "type" is required.');
		}

		if (args !== undefined && !Array.isArray(args)) {
			throw new Error('Expected argument "args" to be Array.');
		}

		this.name = name;
		this.id = uuid();
		this.type = type;
		this.arguments = args ? args : [];

		this.preconditions = [];
		this.postconditions = [];
	}

	setType(type) {
		if (!type) {
			throw new Error('Argument "type" is required.');
		}

		this.type = type;
	}

	addArgument(arg) {
		if (!arg.name) {
			throw new Error('Argument "name" is required.');
		}

		if (!arg.type) {
			throw new Error('Argument "type" is required.');
		}

		for (let i = 0; i < this.arguments.length; i++) {
			if (this.arguments[i].name === arg.name) {
				throw new Error(`Argument "${name}" is already defined.`);
			}
		}

		this.arguments.push(arg);
	}

	addPrecondition(arg) {
		const condition = new OclCondition(arg);

		this.preconditions.push(condition);
	}

	addPostcondition(arg) {
		const condition = new OclCondition(arg);

		this.postconditions.push(condition);
	}
};
