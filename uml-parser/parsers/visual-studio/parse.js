const uuid = require('uuid/v4');
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
		else if (namedElement.referencedTypeMoniker) {
			type = namedElement.referencedTypeMoniker[0].$.LastKnownName;
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

		properties.forEach((property) => {
			const v = {
				id: uuid(),
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
		// Filter to find the first parameter that is the return type.
		const parameter = parameterList.map((parameterListing) => {
			// <parameter> node exists under each <operationHasOwnedParameters> node.
			// Return the value contained within the <parameter> node.
			return parameterListing.parameter[0];
		}).filter((parameter) => {
			return parameter.$.direction === 'Return';
		})[0];

		if (parameter) {
			// TODO: Will the system support Python's multiple object return?'
			return getTypeFromNode(parameter);
		}
		else {
			// Did not find a return type, so function has void type.
			return 'Void';
		}
	}

	// Helper function to get function arguments to array of { name, type }.
	function getArguments(parameters) {
		const args = {};
		const parameterList = parameters[0].operationHasOwnedParameters;

		parameterList.map((parameterListing) => {
			// <parameter> node exists under each <operationHasOwnedParameters> node.
			// Return the value contained within the <parameter> node.
			return parameterListing.parameter[0];
		}).filter((parameter) => {
			return parameter.$.direction === 'In';
		}).forEach((parameter) => {
			const name = parameter.$.name;
			const type = getTypeFromNode(parameter);

			args[name] = type;
		});

		return args;
	}

	// Helper function to take a condition from XML format to standardised format.
	function getConditions(conditions) {
		let c = [];

		function parseConditions(conditions) {
			const split = conditions.split('-----');
			const parsed = split.map((condition) => {
				const result = cfgParser(condition);

				result.id = uuid();

				return result;
			});

			return parsed;
		}

		if (conditions) {
			const constraint = conditions[0].constraint[0];
			const conditionString = constraint.specification[0].literalString[0].$.value;

			c = parseConditions(conditionString);
		}

		return c;
	}

	// Iterate through all methods.
	if (umlClass.ownedOperationsInternal !== undefined) {
		const operations = umlClass.ownedOperationsInternal[0].operation;

		operations.forEach((operation) => {
			// Generic method properties
			const v = {
				id: uuid(),
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
	c.id = uuid();
	c.name = umlClass.$.name;

	// Parse information for class variables and methods.
	c.variables = parseVariables(umlClass);
	c.methods = parseMethods(umlClass);

	return c;
}

function parse(data) {
	return promises.xmlParseString(data).then((uml) => {
		// Enter root item.
		if (uml.modelStoreModel) {
			uml = uml.modelStoreModel;
		}
		else if (uml.logicalClassDesignerModel) {
			uml = uml.logicalClassDesignerModel;
		}

		const classes = {};
		const elements = uml.packagedElements[0];

		function parsePackages(packages) {
			packages.filter((package) => {
				return package.class !== undefined;
			}).map((namedElement) => {
				return namedElement.class[0];
			}).forEach((classElement) => {
				const c = parseClass(classElement);

				classes[c.name] = c;
			});
		}

		if (elements.packageHasNamedElement) {
			parsePackages(elements.packageHasNamedElement);
		}

		if (elements.logicalClassDesignerModelHasTypes) {
			parsePackages(elements.logicalClassDesignerModelHasTypes);
		}

		return classes;
	});
}

module.exports = parse;
