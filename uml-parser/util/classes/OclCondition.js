const uuid = require('uuid/v4');

module.exports = class OclCondition {
	constructor(condition) {
		if (!condition && typeof condition !== 'object') {
			throw new Error('Argument "condition" is required as an object.');
		}

		if (!condition.comparison) {
			throw new Error('"condition" must specify the comparison.');
		}

		if (!Array.isArray(condition.arguments) || condition.arguments.length <= 0) {
			throw new Error('Expected "condition.arguments" to be Array, with at least 1 item.');
		}

		this.id = uuid();
		this.comparison = condition.comparison;

		this.arguments = [];
		condition.arguments.forEach((arg) => {
			this.arguments.push(arg);
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
};
