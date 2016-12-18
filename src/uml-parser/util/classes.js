class AnnotatedUmlClass {
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
		this.type = type;
		this.args = args;

		this.preconditions = {};
		this.postconditions = {};
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
