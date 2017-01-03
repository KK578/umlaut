const path = require('path');
const chai = require('chai');
const chaiAsPromised = require('chai-as-promised');

chai.use(chaiAsPromised);

global.expect = chai.expect;

global.fixtures = {
	models: {
		SimpleMath: {
			uml: path.join(__dirname, '../fixtures/models/SimpleMath/SimpleMath.uml'),
			classdiagram: path.join(__dirname, '../fixtures/models/SimpleMath/SimpleMath.classdiagram'),
		}
	},
	'uml-parser': {
		SimpleMath: path.join(__dirname, '../fixtures/uml-parser/SimpleMath.json')
	},
	'input-generator': {
		SimpleMath: path.join(__dirname, '../fixtures/input-generator/SimpleMath.json')
	}
}

console.log('Test globals loaded.');
