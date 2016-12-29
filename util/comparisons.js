const comparisons = require('./comparisons.json');

function toSmtSymbol(comparison) {
	for (let i = 0; i < comparisons.length; i++) {
		const c = comparisons[i];

		if (c.name === comparison) {
			const symbol = c.smtSymbol ? c.smtSymbol : c.symbol;

			return symbol;
		}
	}

	throw new Error(`Comparison with name "${comparison}" does not exist.`);
}

function toSymbol(comparison) {
	for (let i = 0; i < comparisons.length; i++) {
		const c = comparisons[i];

		if (c.name === comparison) {
			return c.symbol;
		}
	}

	throw new Error(`Comparison with name "${comparison}" does not exist.`);
}

function toName(comparison) {
	for (let i = 0; i < comparisons.length; i++) {
		const c = comparisons[i];

		if (c.symbol === comparison || c.name === comparison) {
			return c.name;
		}
	}

	throw new Error(`Comparison with symbol "${comparison}" does not exist.`);
}

function verifySmtSymbol(comparison) {
	for (let i = 0; i < comparisons.length; i++) {
		const c = comparisons[i];

		if (c.smtSymbol === comparison || c.symbol === comparison) {
			return true;
		}
	}

	return false;
}

module.exports = {
	toName,
	toSymbol,
	toSmtSymbol,
	verifySmtSymbol
};
