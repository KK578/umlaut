const comparisons = require('../../../util/comparisons.js');

function generateTestMethodName(methodName, conditions) {
	const output = conditions.map((condition) => {
		if (condition === 'Valid') {
			return 'Valid';
		}
		else {
			return `Not${comparisons.toName(condition.comparison)}_${condition.arguments.join('_')}`;
		}
	}).join('_');

	return `test_${methodName}_${output}`;
}

function findCondition(preconditions, condition) {
	if (condition === 'Valid') {
		return [condition];
	}

	let idList = '';

	// Split by space as condition id will be "Complement [[UUID]]".
	// TODO: Delete this check, as it is currently held for legacy.
	if (condition.indexOf(' ') > 0) {
		idList = condition.split(' ')[1].split(',');
	}
	else {
		idList = condition.split(',');
	}
	const search = preconditions.filter((c) => {
		return idList.indexOf(c.id) >= 0;
	});

	if (search.length > 0) {
		return search;
	}
	else {
		throw new Error('No valid precondition found.');
	}
}

function readTest(method, variables, test) {
	const id = test.id || test.condition;
	const conditions = findCondition(method.preconditions, id);

	const name = generateTestMethodName(method.name, conditions);
	// TODO: Solve issue of which exception to expect when multiple may error.
	const exception = conditions[0].exception;

	const initialise = Object.keys(test.arguments).map((name) => {
		const result = {
			name: name,
			type: method.arguments[name],
			value: test.arguments[name]
		};

		// Check if current argument is not a method argument
		if (!method.arguments[name]) {
			if (variables[name]) {
				result.type = '#SelfReference';
			}
		}

		return result;
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

function readMethod(m, variables) {
	const tests = m.tests.map((t) => {
		if (t.arguments === 'Unsatisfiable' ||
			t.unsatisfiable === true) {
			return null;
		}

		return readTest(m, variables, t);
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
		return readMethod(uml.methods[name], uml.variables);
	});

	return testClass;
};
