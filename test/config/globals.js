const path = require('path');
const chai = require('chai');
const chaiAsPromised = require('chai-as-promised');

chai.use(chaiAsPromised);

global.expect = chai.expect;

global.fixtures = {
	FullModels: {
		SimpleMath: {
			uml: path.join(__dirname, '../fixtures/full-models/SimpleMath/model.uml'),
			classdiagram: path.join(__dirname, '../fixtures/full-models/SimpleMath/model.classdiagram'),
			'uml-parser': path.join(__dirname, '../fixtures/full-models/SimpleMath/uml-parser.json'),
			'input-generator': path.join(__dirname, '../fixtures/full-models/SimpleMath/input-generator.json')
		},
		DecimalMath: {
			uml: path.join(__dirname, '../fixtures/full-models/DecimalMath/model.uml'),
			classdiagram: path.join(__dirname, '../fixtures/full-models/DecimalMath/model.classdiagram'),
			'uml-parser': path.join(__dirname, '../fixtures/full-models/DecimalMath/uml-parser.json'),
			'input-generator': path.join(__dirname, '../fixtures/full-models/DecimalMath/input-generator.json')
		}
	}
}

console.log('Test globals loaded.');
