const promises = require('../../util/promises.js');
const cfgParser = require('./condition-cfg-parser.js');

function getTypeFromNode(parameter) {
	let type = '';

	if (parameter.type_NamedElement) {
		const namedElement = parameter.type_NamedElement[0];

		if (namedElement.primitiveTypeMoniker) {
			type = namedElement.primitiveTypeMoniker[0].$.LastKnownName;
		}
		else if (namedElement.undefinedTypeMoniker) {
			type = namedElement.undefinedTypeMoniker[0].$.LastKnownName;
		}
		else {
			throw new Error('Could not find type.');
		}
	}
	else {
		type = 'Object';
	}

	return type;
}

function parseVariables(umlClass) {
	const variables = {};

	// Iterate through list of attributes.
	if (umlClass.ownedAttributesInternal !== undefined) {
		const properties = umlClass.ownedAttributesInternal[0].property;

		properties.map((property) => {
			const v = {
				id: property.$.Id,
				name: property.$.name
			};

			v.visibility = property.$.visibility ? property.$.visibility : 'Public';
			v.type = getTypeFromNode(property);

			variables[v.name] = v;
		});
	}

	return variables;
}

function parseMethods(umlClass) {
	const methods = {};

	// Helper function to get function return type.
	function getReturnType(parameters) {
		// Must iterate through all and find first that is a return property.
		const parameterList = parameters[0].operationHasOwnedParameters;

		for (let i = 0; i < parameterList.length; i++) {
			const parameter = parameterList[i].parameter[0];

			// Direction 'Return' indicates the function's return type.
			// TODO: Will the system support Python's multiple object return?'
			if (parameter.$.direction === 'Return') {
				const type = getTypeFromNode(parameter);

				return type;
			}
		}

		// Did not find a return type, so function has void type.
		return 'Void';
	}

	// Helper function to get function arguments to array of { name, type }.
	function getArguments(parameters) {
		const args = {};

		const parameterList = parameters[0].operationHasOwnedParameters;

		for (let i = 0; i < parameterList.length; i++) {
			const parameter = parameterList[i].parameter[0];

			// Direction 'In' indicates a function argument.
			if (parameter.$.direction === 'In') {
				const name = parameter.$.name;
				const type = getTypeFromNode(parameter);

				args[name] = type;
			}
		}

		return args;
	}

	// Helper function to take a condition from XML format to standardised format.
	function getConditions(conditions) {
		let c = [];

		function parseConditions(id, conditions) {
			const split = conditions.split('-----');
			const parsed = split.map((condition, index) => {
				const result = cfgParser(condition);

				result.id = `${id}-${index}`;

				return result;
			});

			return parsed;
		}

		if (conditions) {
			const constraint = conditions[0].constraint[0];
			const conditionString = constraint.specification[0].literalString[0].$.value;
			const id = constraint.$.Id;

			c = parseConditions(id, conditionString);
		}

		return c;
	}

	// Iterate through all methods.
	if (umlClass.ownedOperationsInternal !== undefined) {
		const operations = umlClass.ownedOperationsInternal[0].operation;

		operations.map((operation) => {
			// Generic method properties
			const v = {
				id: operation.$.Id,
				name: operation.$.name
			};

			v.visibility = operation.$.visibility ? operation.$.visibility : 'Public';

			// Types
			v.type = getReturnType(operation.ownedParameters);
			v.arguments = getArguments(operation.ownedParameters);

			// Conditions
			v.preconditions = getConditions(operation.preconditionsInternal);
			v.postconditions = getConditions(operation.postconditionsInternal);

			// TODO: Keep method list as a hashmap of method name?
			methods[v.name] = v;
		});
	}

	return methods;
}

function parseClass(umlClass) {
	const c = {};

	// Locate generic class properties.
	c.id = umlClass.$.Id;
	c.name = umlClass.$.name;

	// Parse information for class variables and methods.
	c.variables = parseVariables(umlClass);
	c.methods = parseMethods(umlClass);

	return c;
}

function parse(data) {
	return promises.xmlParseString(data).then((uml) => {
		// Enter root item.
		const classes = {};

		if (uml.modelStoreModel) {
			uml = uml.modelStoreModel;
		}
		else if (uml.logicalClassDesignerModel) {
			uml = uml.logicalClassDesignerModel;
		}

		uml.packagedElements.map((element) => {
			// All related items are stored as namedElement objects in the package's elements.
			// Iterate through all and for objects representing classes, parse them.
			element.packageHasNamedElement.map((namedElement) => {
				if (namedElement.class) {
					const c = parseClass(namedElement.class[0]);

					classes[c.name] = c;
				}
			});
		});

		return classes;
	});
}

module.exports = parse;
