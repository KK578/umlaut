class AnnotatedUmlClass {
	constructor(name) {
		this.name = name;

		this.variables = {};
		this.methods = {};

		this.invariants = {};
	}

	addVariable(name, type) {
		throw new Error('Not yet implemented');
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

		this.methods[name] = new AnnotatedUmlMethod(name, type, args);
	}

	setMethodType(name, type) {
		throw new Error('Not yet implemented');
	}

	addMethodArgument(name, arg) {
		throw new Error('Not yet implemented');
	}

	AddInvariant(comparison) {
		throw new Error('Not yet implemented');
	}
}

class AnnotatedUmlMethod {
	constructor(name, type, args) {
		this.name = name;
		this.type = type;
		this.args = args;
	}

	setType(type) {
		throw new Error('Not yet implemented');
	}

	addArgument(arg) {
		throw new Error('Not yet implemented');
	}

	addPrecondition(arg) {
		throw new Error('Not yet implemented');
	}

	addPostcondition(arg) {
		throw new Error('Not yet implemented');
	}
}

module.exports = {
	AnnotatedUmlClass,
	AnnotatedUmlMethod
};
