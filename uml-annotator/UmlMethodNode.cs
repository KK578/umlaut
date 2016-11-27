using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Xml;

namespace UmlAnnotator
{
	public class UmlMethodNode
	{
		private string name;
		public string Name
		{
			get { return name; }
		}

		// Even hackier than before.
		public List<OclCondition> Preconditions;
		public List<OclCondition> Postconditions;

		private XmlNode node;
		private XmlNode preconditionNode;
		private XmlNode postconditionNode;
		private Dictionary<string, XmlNode> argumentNodes;
		private XmlNode returnNode;

		public UmlMethodNode(XmlNode node)
		{
			this.node = node;
			this.name = node.Attributes.GetNamedItem("name").Value;

			ParseMethod();

			Preconditions = new List<OclCondition>();
			Postconditions = new List<OclCondition>();
		}

		private void ParseMethod()
		{
			XmlNodeList children = node.ChildNodes;

			foreach (XmlNode child in children)
			{
				if (child.Name == "ownedParameters")
				{
					ParseArguments(child.ChildNodes);
				}
				else if (child.Name == "preconditionsInternal")
				{
					XmlNode constraintNode = child.FirstChild;
					foreach (XmlNode node in constraintNode.ChildNodes)
					{
						if (node.Name == "specification")
						{
							preconditionNode = node.FirstChild.Attributes.GetNamedItem("value");
							break;
						}
					}
				}
				else if (child.Name == "postconditionsInternal")
				{
					XmlNode constraintNode = child.FirstChild;
					foreach (XmlNode node in constraintNode.ChildNodes)
					{
						if (node.Name == "specification")
						{
							postconditionNode = node.FirstChild.Attributes.GetNamedItem("value");
							break;
						}
					}
				}
			}

			XmlDocument doc = node.OwnerDocument;

			// Create nodes in place if they don't already exist.
			if (preconditionNode == null)
			{
				preconditionNode = doc.CreateElement("preconditionsInternal");
				node.AppendChild(preconditionNode);

				preconditionNode = PopulateConstraintNode(preconditionNode);
			}

			if (postconditionNode == null)
			{
				postconditionNode = doc.CreateElement("postconditionsInternal");
				node.AppendChild(postconditionNode);

				postconditionNode = PopulateConstraintNode(postconditionNode);
			}
		}

		private XmlNode PopulateConstraintNode(XmlNode node)
		{
			XmlDocument doc = node.OwnerDocument;
			XmlNode constraintNode = doc.CreateElement("constraint");
			XmlNode specificationNode = doc.CreateElement("specification");
			XmlNode literalStringNode = doc.CreateElement("literalString");
			XmlNode valueNode = doc.CreateAttribute("value");
			valueNode.InnerText = "";
			literalStringNode.Attributes.SetNamedItem(valueNode);
			specificationNode.AppendChild(literalStringNode);
			constraintNode.AppendChild(specificationNode);
			node.AppendChild(constraintNode);

			return valueNode;
		}

		private void ParseArguments(XmlNodeList arguments)
		{
			argumentNodes = new Dictionary<string, XmlNode>();

			foreach (XmlNode child in arguments)
			{
				XmlNode argument = child.ChildNodes[0];
				string direction = argument.Attributes.GetNamedItem("direction").Value;

				if (direction == "In")
				{
					string name = argument.Attributes.GetNamedItem("name").Value;
					argumentNodes.Add(name, argument);
				}
				else if (direction == "Return")
				{
					returnNode = argument;
				}
			}
		}

		public void AddCondition(string type)
		{
			switch (type)
			{
				case "pre":
					Preconditions.Add(new OclCondition());
					break;

				case "post":
					Postconditions.Add(new OclCondition());
					break;
			}
		}

		public void UpdateNodes()
		{
			preconditionNode.InnerText = String.Join(" ", Preconditions);
			postconditionNode.InnerText = String.Join(" ", Postconditions);
		}
	}
}
