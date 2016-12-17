class AnnotatedUmlClass {
	constructor(name) {
		this.name = name;

		this.variables = {};
		this.methods = {};

		this.invariants = {};
	}

	addVariable(name, type) { }

	addMethod(name, type, args) { }
	setMethodType(name, type) { }
	addMethodArgument(name, arg) { }

	AddInvariant(comparison) { }
}

class AnnotatedUmlMethod {
	constructor(name, type, args) { }

	setType(type) { }

	addArgument(arg) { }
	addPrecondition(arg) { }
	addPostcondition(arg) { }
}

module.exports = {
	AnnotatedUmlClass,
	AnnotatedUmlMethod
};
