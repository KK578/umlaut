const comparisons = require('./comparisons.json');

function searchComparisons(filterFunction) {
	const search = comparisons.filter(filterFunction);

	if (search.length > 0) {
		return search[0];
	}
	else {
		return undefined;
	}
}

function toSmtSymbol(comparison) {
	const search = searchComparisons((c) => {
		return c.name === comparison;
	});

	if (search) {
		return search.smtSymbol ? search.smtSymbol : search.symbol;
	}
	else {
		throw new Error(`Comparison with name "${comparison}" does not exist.`);
	}
}

function toSymbol(comparison) {
	const search = searchComparisons((c) => {
		return c.name === comparison;
	});

	if (search) {
		return search.symbol;
	}
	else {
		throw new Error(`Comparison with name "${comparison}" does not exist.`);
	}
}

function toName(comparison) {
	const search = searchComparisons((c) => {
		return c.symbol === comparison || c.name === comparison;
	});

	if (search) {
		return search.name;
	}
	else {
		throw new Error(`Comparison with symbol "${comparison}" does not exist.`);
	}
}

function verifySmtSymbol(comparison) {
	const search = searchComparisons((c) => {
		if (c.smtSymbol !== undefined) {
			if (c.smtSymbol === comparison) {
				return true;
			}
		}
		else if (c.symbol === comparison) {
			return true;
		}
	});

	if (search) {
		return true;
	}
	else {
		return false;
	}
}

module.exports = {
	toName,
	toSymbol,
	toSmtSymbol,
	verifySmtSymbol
};
