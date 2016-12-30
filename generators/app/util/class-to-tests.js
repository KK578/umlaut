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

	const id = condition.split(' ')[1];

	for (let i = 0; i < preconditions.length; i++) {
		const c = preconditions[i];

		if (c.id === id) {
			return c;
		}
	}

	throw new Error('No valid precondition found.');
}

function readTest(method, test) {
	const condition = findCondition(method.preconditions, test.condition);

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
		if (t.arguments === 'Unsatisfiable') {
			return null;
		}

		const test = readTest(m, t);

		return test;
	});

	const postconditions = m.postconditions.map((c) => {
		c.comparison = comparisons.toSymbol(c.comparison);

		return c;
	});

	const method = {
		name: m.name,
		type: m.type,
		postconditions: postconditions,
		tests: tests
	};

	return method;
}

module.exports = (uml) => {
	const testClass = {};

	testClass.name = uml.name;
	testClass.methods = Object.keys(uml.methods).map((name) => {
		return readMethod(uml.methods[name]);
	});

	return testClass;
};
