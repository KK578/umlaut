const comparisons = require('../../../util/comparisons.js');

function generateTestMethodName(methodName, condition) {
	let clean;

	if (condition === 'Valid') {
		clean = 'Valid';
	}
	else {
		clean = `Not${comparisons.toName(condition.comparison)}_${condition.arguments.join('_')}`;
	}

	return `test_${methodName}_${clean}`;
}

function findCondition(preconditions, condition) {
	if (condition === 'Valid') {
		return condition;
	}

	let id = '';

	// Split by space as condition id will be "Complement [[UUID]]".
	// TODO: Delete this check, as it is currently held for legacy.
	if (condition.indexOf(' ') > 0) {
		id = condition.split(' ')[1];
	}
	else {
		id = condition.split(',')[0];
	}
	const search = preconditions.filter((c) => {
		return c.id === id;
	});

	if (search.length > 0) {
		return search[0];
	}
	else {
		throw new Error('No valid precondition found.');
	}
}

function readTest(method, test) {
	const id = test.id || test.condition;
	const condition = findCondition(method.preconditions, id);

	const name = generateTestMethodName(method.name, condition);
	const exception = condition.exception;

	const initialise = Object.keys(test.arguments).map((name) => {
		return {
			name: name,
			type: method.arguments[name],
			value: test.arguments[name]
		};
	});

	const run = [
		{
			name: 'result',
			type: method.type,
			value: {
				type: 'function-call',
				name: method.name,
				arguments: Object.keys(method.arguments)
			}
		}
	];

	const assertions = method.postconditions;

	return {
		name,
		exception,
		initialise,
		run,
		assertions
	};
}

function readMethod(m) {
	const tests = m.tests.map((t) => {
		if (t.arguments === 'Unsatisfiable' ||
			t.unsatisfiable === true) {
			return null;
		}

		return readTest(m, t);
	});

	const postconditions = m.postconditions.map((c) => {
		c.comparison = comparisons.toSymbol(c.comparison);

		return c;
	});

	return {
		name: m.name,
		type: m.type,
		postconditions: postconditions,
		tests: tests
	};
}

module.exports = (uml) => {
	const testClass = {};

	testClass.name = uml.name;
	testClass.methods = Object.keys(uml.methods).map((name) => {
		return readMethod(uml.methods[name]);
	});

	return testClass;
};
