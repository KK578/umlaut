const AnnotatedUmlMethod = require('./AnnotatedUmlMethod.js');
const OclCondition = require('./OclCondition.js');

module.exports = class AnnotatedUmlClass {
	constructor(name) {
		if (!name) {
			throw new Error('Argument "name" is required.');
		}

		this.name = name;

		this.variables = {};
		this.methods = {};

		this.invariants = {};
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
	}

	addMethod(name, type, args) {
		if (!name) {
			throw new Error('Argument "name" is required.');
		}

		if (!type) {
			throw new Error('Argument "type" is required.');
		}

		if (args !== undefined && !Array.isArray(args)) {
			throw new Error('Expected argument "args" to be Array.');
		}

		if (this.methods[name] !== undefined) {
			throw new Error(`Method "${name}" is already defined.`);
		}

		this.methods[name] = new AnnotatedUmlMethod(name, type, args);
	}

	addInvariant(arg) {
		const condition = new OclCondition(arg);

		this.invariants[arg.name] = condition;
	}
};