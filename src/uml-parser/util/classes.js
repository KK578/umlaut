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

		if (this.methods[name] !== undefined) {
			throw new Error(`Method "${name}" is already defined.`);
		}

		this.methods[name] = new AnnotatedUmlMethod(name, type, args);
	}

	addInvariant(comparison) {
		if (!comparison) {
			throw new Error('Argument "comparison" is required.');
		}

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
		this.args = args ? args : [];

		this.preconditions = {};
		this.postconditions = {};
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

		for (let i = 0; i < this.args.length; i++) {
			if (this.args[i].name === arg.name) {
				throw new Error(`Argument "${name}" is already defined.`);
			}
		}

		this.args.push(arg);
	}

	addPrecondition(arg) {
		throw new Error('Not yet implemented');
	}

	addPostcondition(arg) {
		throw new Error('Not yet implemented');
	}
}

class OclCondition {
	constructor(condition) {
		if (!condition) {
			throw new Error('Argument "condition" is required.');
		}

		this.condition = condition;
	}

	setInverted(value) {
		throw new Error('Not yet implemented');
	}

	setException(value) {
		throw new Error('Not yet implemented');
	}
}

module.exports = {
	AnnotatedUmlClass,
	AnnotatedUmlMethod,
	OclCondition
};
