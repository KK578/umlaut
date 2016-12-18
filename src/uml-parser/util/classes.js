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
		if (!condition && typeof condition !== 'object') {
			throw new Error('Argument "condition" is required as an object.');
		}

		if (!condition.comparison) {
			throw new Error('"condition" must specify the comparison.');
		}

		if (!Array.isArray(condition.args) || condition.args.length <= 0) {
			throw new Error('Expected "condition.args" to be Array, with at least 1 item.');
		}

		this.comparison = condition.comparison;

		this.args = [];
		condition.args.map((arg) => {
			this.args.push(arg);
		});

		if (condition.isInverted !== undefined) {
			this.setInverted(condition.isInverted);
		}
	}

	setInverted(value) {
		if (typeof value === 'boolean') {
			this.isInverted = value;
		}
		else {
			throw new Error('Expected "value" to be a Boolean.');
		}
	}

	setException(value) {
		if (!value) {
			throw new Error('Argument "value" is required.');
		}

		this.exception = { type: value };
	}
}

module.exports = {
	AnnotatedUmlClass,
	AnnotatedUmlMethod,
	OclCondition
};
