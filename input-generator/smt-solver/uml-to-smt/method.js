const Smt = require('../util/classes.js');
const comparisons = require('../../../util/comparisons.js');

function convertType(type) {
	switch (type) {
		case 'Integer':
			return 'Int';

		case 'Float':
		case 'Double':
			return 'Real';

		default:
			return type;
	}
}

function declareArguments(args) {
	const commands = [];

	// For every argument to the function, add a declaration to SMT.
	Object.keys(args).forEach((name) => {
		const type = convertType(args[name]);
		const command = new Smt.DeclareConst(name, type);

		// Note the existence of the argument to the class for get-value calls later.
		if (!this.constants[name]) {
			this.constants[name] = true;
		}

		commands.push(command);
	});

	return commands;
}

// Declare the function to SMT.
function declareFunction(method) {
	const commands = [];
	const type = convertType(method.type);
	const args = Object.keys(method.arguments).map((t) => {
		return convertType(method.arguments[t]);
	});
	const command = new Smt.DeclareFunction(method.name, type, args);

	commands.push(command);

	return commands;
}

function assertAllConditions(conditions) {
	const commands = [];

	conditions.forEach((condition) => {
		const comparison = comparisons.toSmtSymbol(condition.comparison);
		const command = new Smt.BooleanExpression(comparison,
			condition.arguments, condition.inverted);

		commands.push(new Smt.Assertion(command));
	});

	return commands;
}

function assertConditionsWithInverts(conditions, complementSet) {
	const commands = [];

	conditions.forEach((condition) => {
		const comparison = comparisons.toSmtSymbol(condition.comparison);
		const command = new Smt.BooleanExpression(comparison,
			condition.arguments, condition.inverted);

		complementSet.forEach((complement) => {
			if (condition === complement) {
				command.setInverted(!command.isInverted);
			}
		});

		commands.push(new Smt.Assertion(command));
	});

	return commands;
}

// Add a layer to the stack so we can pop later and keep the declarations.
function allValidConditions(method) {
	const commands = [];

	commands.push(new Smt.Echo('[[Valid]]'));
	commands.push(new Smt.StackModifier('push'));

	// For each precondition, add it to the stack.
	commands.push(...assertAllConditions(method.preconditions));

	// Declare a variable for the result
	if (method.type !== 'void') {
		const resultType = convertType(method.type);
		const resultDeclare = new Smt.DeclareConst('result', resultType);

		const functionArgs = Object.keys(method.arguments);
		const functionCall = new Smt.FunctionCall(method.name, functionArgs);
		const resultAssert = new Smt.Assertion(
			new Smt.BooleanExpression('=', ['result', functionCall])
		);

		commands.push(resultDeclare);
		commands.push(resultAssert);
	}

	// Add postconditions so that the inputs may be more interesting.
	commands.push(...assertAllConditions(method.postconditions));

	// Check satisfiability and get values of arguments.
	commands.push(new Smt.GetValue(this.getConstants()));
	commands.push(new Smt.StackModifier('pop'));

	return commands;
}

function assertComplementedConditions(conditions, complementSet) {
	const commands = [];

	complementSet.forEach((c, i) => {
		const complementString = c[0].id;

		commands.push(new Smt.Echo(`~~[[${complementString}]]`));
		commands.push(new Smt.StackModifier('push'));
		commands.push(...assertConditionsWithInverts(conditions, c));
		commands.push(new Smt.GetValue(this.getConstants()));
		commands.push(new Smt.StackModifier('pop'));
	});

	return commands;
}

function singularInvalidConditions(method) {
	const complementSet = [];

	// HACK: Currently places each object into the complement set on its own.
	method.preconditions.forEach((c) => {
		complementSet.push([c]);
	});

	const commands = assertComplementedConditions.call(this, method.preconditions, complementSet);

	return commands;
}

function optionalConditions(method) {
	if (!Array.isArray(method.optionalPreconditions) ||
		method.optionalPreconditions.length === 0) {
		return [];
	}

	const commands = [];

	// Add a layer to the stack so we can pop later and keep the declarations.
	commands.push(new Smt.Echo('[[ValidOptional]]'));
	commands.push(new Smt.StackModifier('push'));

	// Optional preconditions are bound under the main preconditions, so they must also be
	//  fulfilled.
	// For each precondition, add it to the stack.
	commands.push(...assertAllConditions(method.preconditions));

	// Generate input when all optional preconditions are fulfilled.
	commands.push(new Smt.StackModifier('push'));
	commands.push(...assertAllConditions(method.optionalPreconditions));
	commands.push(new Smt.GetValue(this.getConstants()));
	commands.push(new Smt.StackModifier('pop'));

	// Generate inputs when one optional precondition is complemented.
	const complementSet = [];

	// HACK: Currently places each object into the complement set on its own.
	method.optionalPreconditions.forEach((c) => {
		complementSet.push([c]);
	});
	commands.push(...assertComplementedConditions.call(this,
		method.optionalPreconditions, complementSet));

	commands.push(new Smt.StackModifier('pop'));

	return commands;
}

module.exports = class SmtMethod {
	constructor(method) {
		this.commands = [];
		this.constants = {};

		this.commands = this.commands.concat(
			declareArguments.call(this, method.arguments),
			declareFunction.call(this, method),
			allValidConditions.call(this, method),
			singularInvalidConditions.call(this, method),
			optionalConditions.call(this, method)
		);
	}

	getConstants() {
		return Object.keys(this.constants);
	}

	getCommands() {
		return this.commands;
	}
};
