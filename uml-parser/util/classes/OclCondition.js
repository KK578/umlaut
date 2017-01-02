module.exports = class OclCondition {
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
		condition.args.forEach((arg) => {
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
};
