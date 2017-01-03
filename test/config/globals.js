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
	}
}

console.log('Test globals loaded.');
