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

module.exports = {
	AnnotatedUmlClass
};
