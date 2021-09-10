import { Meta } from "@storybook/react/types-6-0";
import { Story } from "@storybook/react";
import MultipleSelector, { Props, Choice } from "./MultipleSelector";

const choices: Choice[] = [{ label: 'A', id: 'a' }, { label: 'B', id: 'b' }, { label: 'C', id: 'c' }, { label: 'D', id: 'd' }, { label: 'E', id: 'e' }, { label: 'F', id: 'f' }, { label: 'G', id: 'g' }, { label: 'H', id: 'h' }, { label: 'I', id: 'i' }, { label: 'J', id: 'j' }, { label: 'K', id: 'k' }, { label: 'L', id: 'l' }, { label: 'M', id: 'm' }, { label: 'N', id: 'n' }];

export default {
  title: "Components/MultipleSelector",
  component: MultipleSelector,
  args: {
    label: '',
    popUpKey: 'Mul-Selector-key',
    choiceSections: [{ choices }],
    name: 'Choice',
    placeholder: 'please select choices',
    id: 'Mul-Selector-id',
    handleSelect: ({ value, name }) => { console.log({ value, name })},
    style: { width: '300px' }
  }
} as Meta<Props>;

// Create a master template for mapping args to render the Button component
const Template: Story<Props> = (args) => <MultipleSelector {...args} />;

// Reuse that template for creating different stories
export const Normal = Template.bind({});
export const WithSingleChoice = Template.bind({});
WithSingleChoice.args = { ...Normal.args, choiceSections: [{ sectionName: 'Single Choice', choices: [{ label: 'Special One', singleChoice: true }]}, { sectionName: 'Multiple Choice', choices: choices }] };
export const WithSectionPrefix =  Template.bind({});
WithSectionPrefix.args = { ...Normal.args, choiceSections: [{ sectionName: 'Single Choice', sectionPrefix: 'single-prefix', choices: [{ label: 'Special One', singleChoice: true }]}, { sectionName: 'Multiple Choice', choices: choices, sectionPrefix: 'mul-prefix' }] };
