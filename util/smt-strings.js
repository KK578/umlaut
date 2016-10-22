class SmtStrings {
	declareConst(name, type) {
		return `(declare-const ${name} ${type})`;
	}

	declareFunction(name, args, type) {
		if (args instanceof Array) {
			return this.declareFunction(name, args.join(' '), type);
		}

		return `(declare-fun ${name} (${args}) ${type})`;
	}

	makeAssertion(assertionType, left, right) {
		return `(assert (${assertionType} ${left} ${right}))`;
	}

	makeInvertedAssertion(assertionType, left, right) {
		return `(assert (not (${assertionType} ${left} ${right})))`;
	}

	makeFunctionCall(name, args) {
		if (args instanceof Array) {
			return this.makeFunctionCall(name, args.join(' '));
		}

		return `(${name} ${args})`;
	}

	stackPush() {
		return '(push)';
	}

	stackPop() {
		return '(pop)';
	}

	checkSat() {
		return '(check-sat)';
	}

	getModel() {
		return '(get-model)';
	}

	getValues(args) {
		if (args instanceof Array) {
			return this.getValues(args.join(' '));
		}

		return `(get-value (${args}))`;
	}
}

module.exports = SmtStrings;
