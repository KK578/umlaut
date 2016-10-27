function findClosingParen(text, start) {
	let end = start;
	let count = 1;

	while (count > 0) {
		const c = text[++end];

		if (c === '(') {
			count++;
		}
		else if (c === ')') {
			count--;
		}
	}

	return end;
}

function parseValues(text) {
	// Strip outer parentheses.
	text = text.slice(1, text.length - 1);

	const values = [];
	// Find the first occurance of a space and split on that to determine name and value.
	const objectify = (s) => {
		const index = s.indexOf(' ');
		const name = s.substring(0, index);
		const value = s.substring(index + 1);

		return { [name]: value };
	};

	for (let i = 0; i < text.length; i++) {
		if (text[i] === '(') {
			i++;
			const oppositeParen = findClosingParen(text, i);
			const valueString = text.slice(i, oppositeParen);

			values.push(objectify(valueString));
			i = oppositeParen;
		}
	}

	return Object.assign.apply(null, values);
}

function parseCondition(text) {
	const split = text.split('\n');
	const condition = split[0];
	let args = {};

	if (split[1] === 'sat') {
		const values = split.slice(2).join('');
		args = parseValues(values);
	}

	return {
		condition,
		args
	}
}

function parseZ3(text) {
	let split = text.split('-----');
	// Ignore first as it will be empty.
	split = split.slice(1);

	const results = split.map(parseCondition);

	return results;
}

module.exports = {
	parseZ3
}
