class AnnotatedUmlClass {
	constructor(name) {
		this.name = name;

		this.variables = {};
		this.methods = {};

		this.invariants = {};
	}

	addVariable(name, type) { }

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

	setMethodType(name, type) { }
	addMethodArgument(name, arg) { }

	AddInvariant(comparison) { }
}

class AnnotatedUmlMethod {
	constructor(name, type, args) {
		this.name = name;
		this.type = type;
		this.args = args;
	}

	setType(type) { }

	addArgument(arg) { }
	addPrecondition(arg) { }
	addPostcondition(arg) { }
}

module.exports = {
	AnnotatedUmlClass,
	AnnotatedUmlMethod
};
