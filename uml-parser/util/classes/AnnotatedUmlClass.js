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

	addVariable(variableObject) {
		if (typeof variableObject !== 'string' && !variableObject.name) {
			throw new Error('Property "name" is required.');
		}

		const name = variableObject.name ? variableObject.name : variableObject;

		if (this.variables[name] !== undefined) {
			throw new Error(`Variable "${name}" is already defined.`);
		}

		const v = {
			name: name,
			id: uuid(),
			type: variableObject.type ? variableObject.type : 'Object',
			visibility: variableObject.visibility ? variableObject.visibility : 'Public'
		};

		this.variables[name] = v;
	}

	addMethod(methodObject) {
		if (!methodObject.name) {
			throw new Error('Property "name" is required.');
		}

		if (!methodObject.type) {
			throw new Error('Property "type" is required.');
		}

		if (methodObject.arguments !== undefined && !Array.isArray(methodObject.arguments)) {
			throw new Error('Expected property "arguments" to be an Array.');
		}

		if (this.methods[methodObject.name] !== undefined) {
			throw new Error(`Method "${methodObject.name}" is already defined.`);
		}

		this.methods[methodObject.name] = new AnnotatedUmlMethod(methodObject);
	}

	addInvariant(arg) {
		const condition = new OclCondition(arg);

		this.invariants.push(condition);
	}
};
