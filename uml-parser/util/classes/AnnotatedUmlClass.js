const uuid = require('uuid/v4');

const AnnotatedUmlMethod = require('./AnnotatedUmlMethod.js');
const OclCondition = require('./OclCondition.js');

module.exports = class AnnotatedUmlClass {
	constructor(classObject) {
		if (typeof classObject !== 'string' && !classObject.name) {
			throw new Error('Property "name" is required.');
		}

		this.name = classObject.name ? classObject.name : classObject;
		this.id = uuid();

		this.visibility = classObject.visibility ? classObject.visibility : 'Public';
		this.type = classObject.type ? classObject.type : 'Object';

		this.variables = {};
		this.methods = {};

		this.invariants = [];
	}

	addVariable(name, type) {
		if (!name) {
			throw new Error('Argument "name" is required.');
		}

		if (!type) {
			type = 'object';
		}

		if (this.variables[name] !== undefined) {
			throw new Error(`Variable "${name}" is already defined.`);
		}

		this.variables[name] = { type };
		this.variables[name].id = uuid();
	}

	addMethod(methodObject) {
		if (!methodObject.name) {
			throw new Error('Property "name" is required.');
		}

		if (!methodObject.type) {
			throw new Error('Property "type" is required.');
		}

		if (methodObject.arguments !== undefined && !Array.isArray(methodObject.arguments)) {
			throw new Error('Expected property "arguments" to be Array.');
		}

		if (this.methods[name] !== undefined) {
			throw new Error(`Method "${name}" is already defined.`);
		}

		this.methods[name] = new AnnotatedUmlMethod(methodObject);
		this.methods[name].id = uuid();
	}

	addInvariant(arg) {
		const condition = new OclCondition(arg);

		this.invariants.push(condition);
	}

	getMethod(name) {
		return this.methods[name];
	}
};
