module.exports = class SmtStackModifier {
	constructor(mode) {
		if (mode) {
			if (mode !== 'push' && mode !== 'pop') {
				throw new Error('StackModifier "mode" may only be "push" or "pop".');
			}
		}
		else {
			mode = 'push';
		}

		this.mode = mode;
	}

	toString() {
		return `(${this.mode})`;
	}
};
