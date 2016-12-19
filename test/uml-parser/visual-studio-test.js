const chai = require('chai');
const chaiAsPromised = require("chai-as-promised");
const path = require('path');

chai.use(chaiAsPromised);

const expect = chai.expect;

const testee = require('../../src/uml-parser/index.js');

describe('Uml Parser Entry Point', () => {
	it('should parse SimpleMath test fixture', () => {
		const fixture = path.join(__dirname, '../fixtures/SimpleMath/ModelDefinition/SimpleMath.uml');
		const promise = testee(fixture);

		return expect(promise).to.be.fulfilled;
	});
});
