const uuid = require('uuid/v4');
const OclCondition = require('./OclCondition.js');

module.exports = class AnnotatedUmlMethod {
	constructor(methodObject) {
		if (!methodObject.name) {
			throw new Error('Property "name" is required.');
		}

		if (!methodObject.type) {
			throw new Error('Property "type" is required.');
		}

		if (methodObject.arguments !== undefined && !Array.isArray(methodObject.arguments)) {
			throw new Error('Expected property "args" to be Array.');
		}

		this.name = methodObject.name;
		this.id = uuid();
		this.visibility = methodObject.visibility ? methodObject.visibility : 'Public';
		this.type = methodObject.type;
		this.arguments = methodObject.arguments ? methodObject.arguments : [];

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
